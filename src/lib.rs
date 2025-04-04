use byteorder::{BigEndian, ByteOrder};
use libc::{ftruncate, mmap, MAP_SHARED, PROT_READ, PROT_WRITE};
use nix::{
    errno::Errno,
    fcntl::{fcntl, FcntlArg, OFlag},
    sys::socket::{
        recvmsg, sendmsg, ControlMessage, ControlMessageOwned, MsgFlags, RecvMsg, UnixAddr,
    },
};
use std::{
    ffi::{c_void, CString},
    io::Write,
    marker::PhantomData,
    ops::Deref,
    ptr,
    sync::Arc,
    thread::sleep,
    time::Duration,
};

use std::{
    collections::HashMap,
    fs::OpenOptions,
    io::{Error, ErrorKind, IoSlice},
    os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd},
    rc::Rc,
};
#[cfg(target_os = "linux")]
mod os_specific_imports {
    pub use nix::sys::memfd::{memfd_create, MemFdCreateFlag};
}
#[cfg(target_os = "macos")]
mod os_specific_imports {
    pub use libc::{shm_open, shm_unlink};
    pub use rand::prelude::*;
}
use os_specific_imports::*;

const CHUNK_SIZE: usize = 1024;
const MAX_FDS_PER_CHUNK: usize = 5;
const NOOP_TAG: [u8; 4] = *b"NOOP";

#[repr(C)]
#[derive(Copy, Clone)]
pub enum LogLevel {
    Emergency = 0,
    Alert = 1,
    Critical = 2,
    Error = 3,
    Warning = 4,
    Notice = 5,
    Info = 6,
    Debug = 7,
}

impl TryFrom<i32> for LogLevel {
    type Error = &'static str;

    fn try_from(value: i32) -> Result<Self, <Self as TryFrom<i32>>::Error> {
        match value {
            0 => Ok(LogLevel::Emergency),
            1 => Ok(LogLevel::Alert),
            2 => Ok(LogLevel::Critical),
            3 => Ok(LogLevel::Error),
            4 => Ok(LogLevel::Warning),
            5 => Ok(LogLevel::Notice),
            6 => Ok(LogLevel::Info),
            7 => Ok(LogLevel::Debug),
            _ => Err("Invalid value for LogLevel"),
        }
    }
}

impl IsoxTermSerialize for LogLevel {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        let i = *self as i32;
        ctx.data.extend_from_slice(&i.to_be_bytes());
    }
}

impl IsoxTermDeserialize for LogLevel {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> LogLevel {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<i32>());
        ctx.data = rest;
        i32::from_be_bytes(bytes.try_into().unwrap())
            .try_into()
            .expect("Invalid log level")
    }
}

#[derive(Debug)]
pub struct RawPointer<T> {
    pub(crate) ptr: usize,
    pub(crate) struct_type: PhantomData<T>,
}

impl<T> RawPointer<T> {
    pub fn new(data: *const T) -> RawPointer<T> {
        RawPointer {
            ptr: data as usize,
            struct_type: PhantomData,
        }
    }
    pub fn as_ptr(&self) -> *const T {
        self.ptr as *const T
    }
}

impl<T> Deref for RawPointer<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*(self.ptr as *const T) }
    }
}

impl<T> Copy for RawPointer<T> {}

impl<T> Clone for RawPointer<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> PartialEq for RawPointer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Eq for RawPointer<T> {}

impl<T> std::hash::Hash for RawPointer<T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.ptr.hash(state);
    }
}

impl IsoxTermSerialize for RawPointer<c_void> {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        ctx.data.extend_from_slice(&self.ptr.to_be_bytes());
    }
}

impl IsoxTermDeserialize for RawPointer<c_void> {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> RawPointer<c_void> {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<usize>());
        ctx.data = rest;
        RawPointer {
            ptr: usize::from_be_bytes(bytes.try_into().unwrap()),
            struct_type: PhantomData,
        }
    }
}

pub struct IsoxTermSerializationContext {
    data: Vec<u8>,
    fds: Vec<Arc<OwnedFd>>,
}

impl IsoxTermSerializationContext {
    pub fn new() -> Self {
        IsoxTermSerializationContext {
            data: Vec::new(),
            fds: Vec::new(),
        }
    }
}

pub struct IsoxTermDeserializationContext<'a> {
    data: &'a [u8],
    fds: Vec<Arc<OwnedFd>>,
}

impl<'a> IsoxTermDeserializationContext<'a> {
    pub fn new(data: &'a [u8], fds: Vec<Arc<OwnedFd>>) -> Self {
        IsoxTermDeserializationContext { data, fds }
    }
}

pub trait IsoxTermSerialize {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext);
}

pub trait IsoxTermDeserialize {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> Self;
}

impl IsoxTermSerialize for bool {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        if *self {
            ctx.data.push(1 as u8);
        } else {
            ctx.data.push(0 as u8);
        }
    }
}

impl IsoxTermDeserialize for bool {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> bool {
        let value = ctx.data[0];
        ctx.data = &ctx.data[1..];
        if value == 0 {
            false
        } else {
            true
        }
    }
}

impl IsoxTermSerialize for i64 {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        ctx.data.extend_from_slice(&self.to_be_bytes());
    }
}

impl IsoxTermDeserialize for i64 {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> i64 {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<i64>());
        ctx.data = rest;
        i64::from_be_bytes(bytes.try_into().unwrap())
    }
}

impl IsoxTermSerialize for u64 {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        ctx.data.extend_from_slice(&self.to_be_bytes());
    }
}

impl IsoxTermDeserialize for u64 {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> u64 {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<u64>());
        ctx.data = rest;
        u64::from_be_bytes(bytes.try_into().unwrap())
    }
}

impl IsoxTermSerialize for usize {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        ctx.data.extend_from_slice(&self.to_be_bytes());
    }
}

impl IsoxTermDeserialize for usize {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> usize {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<usize>());
        ctx.data = rest;
        usize::from_be_bytes(bytes.try_into().unwrap())
    }
}

impl IsoxTermSerialize for f64 {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        ctx.data.extend_from_slice(&self.to_be_bytes());
    }
}

impl IsoxTermDeserialize for f64 {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> f64 {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<f64>());
        ctx.data = rest;
        f64::from_be_bytes(bytes.try_into().unwrap())
    }
}

impl IsoxTermSerialize for String {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        let utf8 = self.as_bytes();
        let len = utf8.len() as u16;
        if len > u16::MAX {
            panic!("String is too long to be prefixed with a u8 length");
        }
        ctx.data.extend_from_slice(&len.to_be_bytes());
        ctx.data.extend_from_slice(&utf8);
    }
}

impl IsoxTermDeserialize for String {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> String {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<u16>());
        ctx.data = rest;
        let len = u16::from_be_bytes(bytes.try_into().unwrap()) as usize;

        let (bytes, rest) = ctx.data.split_at(len);
        ctx.data = rest;
        String::from_utf8(bytes.to_vec()).unwrap()
    }
}

impl<T> IsoxTermSerialize for Rc<T>
where
    T: IsoxTermSerialize,
{
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        self.as_ref().isox_term_serialize(ctx)
    }
}

impl<T> IsoxTermDeserialize for Rc<T>
where
    T: IsoxTermDeserialize,
{
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> Rc<T> {
        Rc::new(T::isox_term_deserialize(ctx))
    }
}

impl<T> IsoxTermSerialize for Arc<T>
where
    T: IsoxTermSerialize,
{
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        self.as_ref().isox_term_serialize(ctx)
    }
}

impl<T> IsoxTermDeserialize for Arc<T>
where
    T: IsoxTermDeserialize,
{
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> Arc<T> {
        Arc::new(T::isox_term_deserialize(ctx))
    }
}

impl<K, V> IsoxTermSerialize for HashMap<K, V>
where
    K: IsoxTermSerialize,
    V: IsoxTermSerialize,
{
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        let len = self.len() as u16;
        if len > u16::MAX {
            panic!("Map is too big");
        }
        ctx.data.extend_from_slice(&len.to_be_bytes());
        for (key, value) in self {
            key.isox_term_serialize(ctx);
            value.isox_term_serialize(ctx);
        }
    }
}

impl IsoxTermDeserialize for HashMap<Arc<Term>, Arc<Term>> {
    fn isox_term_deserialize(
        ctx: &mut IsoxTermDeserializationContext,
    ) -> HashMap<Arc<Term>, Arc<Term>> {
        let mut map = HashMap::new();

        // get the size of the map
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<u16>());
        ctx.data = rest;
        let size = u16::from_be_bytes(bytes.try_into().unwrap()) as usize;

        for _ in 0..size {
            let key = Arc::isox_term_deserialize(ctx);
            let value = Arc::isox_term_deserialize(ctx);
            map.insert(key, value);
        }
        map
    }
}

impl<T> IsoxTermSerialize for Vec<T>
where
    T: IsoxTermSerialize,
{
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        let len = self.len() as u16;
        if len > u16::MAX {
            panic!("List is too long");
        }
        ctx.data.extend_from_slice(&len.to_be_bytes());
        for term in self {
            term.isox_term_serialize(ctx);
        }
    }
}

impl IsoxTermDeserialize for Vec<Arc<Term>> {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> Vec<Arc<Term>> {
        // get the length of the list
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<u16>());
        ctx.data = rest;
        let size = u16::from_be_bytes(bytes.try_into().unwrap()) as usize;

        let mut vec = Vec::with_capacity(size);

        for _ in 0..size {
            vec.push(Arc::isox_term_deserialize(ctx));
        }
        vec
    }
}

#[derive(Debug, Clone)]
pub enum ToExtensionMsg {
    InitCommand {
        arguments: Arc<Term>,
    },
    QueryCommand {
        command_id: u64,
        arguments: Arc<Term>,
    },
    CreateInstanceCommand {
        command_id: u64,
        arguments: Arc<Term>,
    },
    QueryInstanceCommand {
        command_id: u64,
        instance: Arc<Term>,
        arguments: Arc<Term>,
    },
    UpdateInstanceCommand {
        command_id: u64,
        instance: Arc<Term>,
        arguments: Arc<Term>,
    },
    DestroyInstanceCommand {
        command_id: u64,
        instance: Arc<Term>,
    },
    ResourceDestructorCommand {
        resource_type_id: u64,
        resource_data: RawPointer<c_void>,
    },
}

#[repr(u8)]
enum ToExtensionMsgTags {
    InitCommandTag = 1,
    QueryCommandTag = 2,
    CreateInstanceCommandTag = 3,
    QueryInstanceCommandTag = 4,
    UpdateInstanceCommandTag = 5,
    DestroyInstanceCommandTag = 6,
    ResourceDestructorCommandTag = 7,
}

impl ToExtensionMsgTags {
    fn from(value: u8) -> Self {
        match value {
            1 => ToExtensionMsgTags::InitCommandTag,
            2 => ToExtensionMsgTags::QueryCommandTag,
            3 => ToExtensionMsgTags::CreateInstanceCommandTag,
            4 => ToExtensionMsgTags::QueryInstanceCommandTag,
            5 => ToExtensionMsgTags::UpdateInstanceCommandTag,
            6 => ToExtensionMsgTags::DestroyInstanceCommandTag,
            7 => ToExtensionMsgTags::ResourceDestructorCommandTag,
            _ => panic!("Unknown extension message tag: {}", value),
        }
    }
}

impl IsoxTermSerialize for ToExtensionMsg {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        match self {
            ToExtensionMsg::InitCommand { arguments } => {
                ctx.data.push(ToExtensionMsgTags::InitCommandTag as u8);
                arguments.isox_term_serialize(ctx);
            }
            ToExtensionMsg::QueryCommand {
                command_id,
                arguments,
            } => {
                ctx.data.push(ToExtensionMsgTags::QueryCommandTag as u8);
                command_id.isox_term_serialize(ctx);
                arguments.isox_term_serialize(ctx);
            }
            ToExtensionMsg::CreateInstanceCommand {
                command_id,
                arguments,
            } => {
                ctx.data
                    .push(ToExtensionMsgTags::CreateInstanceCommandTag as u8);
                command_id.isox_term_serialize(ctx);
                arguments.isox_term_serialize(ctx);
            }
            ToExtensionMsg::QueryInstanceCommand {
                command_id,
                instance,
                arguments,
            } => {
                ctx.data
                    .push(ToExtensionMsgTags::QueryInstanceCommandTag as u8);
                command_id.isox_term_serialize(ctx);
                instance.isox_term_serialize(ctx);
                arguments.isox_term_serialize(ctx);
            }
            ToExtensionMsg::UpdateInstanceCommand {
                command_id,
                instance,
                arguments,
            } => {
                ctx.data
                    .push(ToExtensionMsgTags::UpdateInstanceCommandTag as u8);
                command_id.isox_term_serialize(ctx);
                instance.isox_term_serialize(ctx);
                arguments.isox_term_serialize(ctx);
            }
            ToExtensionMsg::DestroyInstanceCommand {
                command_id,
                instance,
            } => {
                ctx.data
                    .push(ToExtensionMsgTags::DestroyInstanceCommandTag as u8);
                command_id.isox_term_serialize(ctx);
                instance.isox_term_serialize(ctx);
            }
            ToExtensionMsg::ResourceDestructorCommand {
                resource_type_id,
                resource_data,
            } => {
                ctx.data
                    .push(ToExtensionMsgTags::ResourceDestructorCommandTag as u8);
                resource_type_id.isox_term_serialize(ctx);
                resource_data.isox_term_serialize(ctx);
            }
        }
    }
}

impl IsoxTermDeserialize for ToExtensionMsg {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> ToExtensionMsg {
        let type_id = ctx.data[0];
        ctx.data = &ctx.data[1..];
        match ToExtensionMsgTags::from(type_id) {
            ToExtensionMsgTags::InitCommandTag => ToExtensionMsg::InitCommand {
                arguments: Arc::isox_term_deserialize(ctx),
            },
            ToExtensionMsgTags::QueryCommandTag => ToExtensionMsg::QueryCommand {
                command_id: u64::isox_term_deserialize(ctx),
                arguments: Arc::isox_term_deserialize(ctx),
            },
            ToExtensionMsgTags::CreateInstanceCommandTag => ToExtensionMsg::CreateInstanceCommand {
                command_id: u64::isox_term_deserialize(ctx),
                arguments: Arc::isox_term_deserialize(ctx),
            },
            ToExtensionMsgTags::QueryInstanceCommandTag => ToExtensionMsg::QueryInstanceCommand {
                command_id: u64::isox_term_deserialize(ctx),
                instance: Arc::isox_term_deserialize(ctx),
                arguments: Arc::isox_term_deserialize(ctx),
            },
            ToExtensionMsgTags::UpdateInstanceCommandTag => ToExtensionMsg::UpdateInstanceCommand {
                command_id: u64::isox_term_deserialize(ctx),
                instance: Arc::isox_term_deserialize(ctx),
                arguments: Arc::isox_term_deserialize(ctx),
            },
            ToExtensionMsgTags::DestroyInstanceCommandTag => {
                ToExtensionMsg::DestroyInstanceCommand {
                    command_id: u64::isox_term_deserialize(ctx),
                    instance: Arc::isox_term_deserialize(ctx),
                }
            }
            ToExtensionMsgTags::ResourceDestructorCommandTag => {
                ToExtensionMsg::ResourceDestructorCommand {
                    resource_type_id: u64::isox_term_deserialize(ctx),
                    resource_data: RawPointer::isox_term_deserialize(ctx),
                }
            }
        }
    }
}

pub enum FromExtensionMsg {
    QueryResponse {
        command_id: u64,
        term: Arc<Term>,
    },
    CreateInstanceResponse {
        command_id: u64,
        instance: Arc<Term>,
    },
    QueryInstanceResponse {
        command_id: u64,
        term: Arc<Term>,
    },
    UpdateInstanceResponse {
        command_id: u64,
        term: Arc<Term>,
    },
    DestroyInstanceResponse {
        command_id: u64,
        term: Arc<Term>,
    },
    SendRequest {
        pid: Arc<Term>,
        msg: Arc<Term>,
    },
    PluginFailed {
        term: Arc<Term>,
    },
    Log {
        level: LogLevel,
        scope: String,
        message: String,
    },
}

#[repr(u8)]
enum FromExtensionMsgTags {
    QueryResponseTag = 1,
    CreateInstanceResponseTag = 2,
    QueryInstanceResponseTag = 3,
    UpdateInstanceResponseTag = 4,
    DestroyInstanceResponseTag = 5,
    SendRequestTag = 6,
    PluginFailedTag = 7,
    LogTag = 8,
}

impl FromExtensionMsgTags {
    fn from(value: u8) -> Self {
        match value {
            1 => FromExtensionMsgTags::QueryResponseTag,
            2 => FromExtensionMsgTags::CreateInstanceResponseTag,
            3 => FromExtensionMsgTags::QueryInstanceResponseTag,
            4 => FromExtensionMsgTags::UpdateInstanceResponseTag,
            5 => FromExtensionMsgTags::DestroyInstanceResponseTag,
            6 => FromExtensionMsgTags::SendRequestTag,
            7 => FromExtensionMsgTags::PluginFailedTag,
            8 => FromExtensionMsgTags::LogTag,
            _ => panic!("Unknown plugin response tag: {}", value),
        }
    }
}

impl IsoxTermSerialize for FromExtensionMsg {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        match self {
            FromExtensionMsg::PluginFailed { term } => {
                ctx.data.push(FromExtensionMsgTags::PluginFailedTag as u8);
                term.isox_term_serialize(ctx);
            }
            FromExtensionMsg::Log {
                level,
                scope,
                message,
            } => {
                ctx.data.push(FromExtensionMsgTags::LogTag as u8);
                level.isox_term_serialize(ctx);
                scope.isox_term_serialize(ctx);
                message.isox_term_serialize(ctx);
            }
            FromExtensionMsg::QueryResponse { command_id, term } => {
                ctx.data.push(FromExtensionMsgTags::QueryResponseTag as u8);
                command_id.isox_term_serialize(ctx);
                term.isox_term_serialize(ctx);
            }
            FromExtensionMsg::CreateInstanceResponse {
                command_id,
                instance,
            } => {
                ctx.data
                    .push(FromExtensionMsgTags::CreateInstanceResponseTag as u8);
                command_id.isox_term_serialize(ctx);
                instance.isox_term_serialize(ctx);
            }
            FromExtensionMsg::QueryInstanceResponse { command_id, term } => {
                ctx.data
                    .push(FromExtensionMsgTags::QueryInstanceResponseTag as u8);
                command_id.isox_term_serialize(ctx);
                term.isox_term_serialize(ctx);
            }
            FromExtensionMsg::UpdateInstanceResponse { command_id, term } => {
                ctx.data
                    .push(FromExtensionMsgTags::UpdateInstanceResponseTag as u8);
                command_id.isox_term_serialize(ctx);
                term.isox_term_serialize(ctx);
            }
            FromExtensionMsg::DestroyInstanceResponse { command_id, term } => {
                ctx.data
                    .push(FromExtensionMsgTags::DestroyInstanceResponseTag as u8);
                command_id.isox_term_serialize(ctx);
                term.isox_term_serialize(ctx);
            }
            FromExtensionMsg::SendRequest { pid, msg } => {
                ctx.data.push(FromExtensionMsgTags::SendRequestTag as u8);
                pid.isox_term_serialize(ctx);
                msg.isox_term_serialize(ctx);
            }
        }
    }
}

impl IsoxTermDeserialize for FromExtensionMsg {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> FromExtensionMsg {
        let type_id = ctx.data[0];
        ctx.data = &ctx.data[1..];
        match FromExtensionMsgTags::from(type_id) {
            FromExtensionMsgTags::QueryResponseTag => FromExtensionMsg::QueryResponse {
                command_id: u64::isox_term_deserialize(ctx),
                term: Arc::isox_term_deserialize(ctx),
            },
            FromExtensionMsgTags::CreateInstanceResponseTag => {
                FromExtensionMsg::CreateInstanceResponse {
                    command_id: u64::isox_term_deserialize(ctx),
                    instance: Arc::isox_term_deserialize(ctx),
                }
            }
            FromExtensionMsgTags::QueryInstanceResponseTag => {
                FromExtensionMsg::QueryInstanceResponse {
                    command_id: u64::isox_term_deserialize(ctx),
                    term: Arc::isox_term_deserialize(ctx),
                }
            }
            FromExtensionMsgTags::UpdateInstanceResponseTag => {
                FromExtensionMsg::UpdateInstanceResponse {
                    command_id: u64::isox_term_deserialize(ctx),
                    term: Arc::isox_term_deserialize(ctx),
                }
            }
            FromExtensionMsgTags::DestroyInstanceResponseTag => {
                FromExtensionMsg::DestroyInstanceResponse {
                    command_id: u64::isox_term_deserialize(ctx),
                    term: Arc::isox_term_deserialize(ctx),
                }
            }
            FromExtensionMsgTags::SendRequestTag => FromExtensionMsg::SendRequest {
                pid: Arc::isox_term_deserialize(ctx),
                msg: Arc::isox_term_deserialize(ctx),
            },
            FromExtensionMsgTags::PluginFailedTag => FromExtensionMsg::PluginFailed {
                term: Arc::isox_term_deserialize(ctx),
            },
            FromExtensionMsgTags::LogTag => FromExtensionMsg::Log {
                level: LogLevel::isox_term_deserialize(ctx),
                scope: String::isox_term_deserialize(ctx),
                message: String::isox_term_deserialize(ctx),
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct ShmSegment {
    pub size: usize,
    fd: Arc<OwnedFd>,
    addr: Arc<usize>,
}

impl ShmSegment {
    pub fn new(size: usize) -> ShmSegment {
        unsafe {
            let fd = ShmSegment::create_shm_segment();
            ftruncate(fd, size as i64);

            let addr = mmap(
                std::ptr::null_mut(),
                size,
                PROT_READ | PROT_WRITE,
                MAP_SHARED,
                fd,
                0,
            );
            if addr.is_null() {
                panic!("Failed to mmap");
            }
            ShmSegment {
                fd: Arc::new(OwnedFd::from_raw_fd(fd)),
                size,
                addr: Arc::new(addr as usize),
            }
        }
    }

    pub fn get_addr(&self) -> *const c_void {
        let addr: usize = *self.addr;
        addr as *const c_void
    }

    #[cfg(target_os = "linux")]
    unsafe fn create_shm_segment() -> RawFd {
        use std::os::fd::IntoRawFd;

        let owned_fd = memfd_create(
            CString::new("isox").unwrap().as_c_str(),
            MemFdCreateFlag::MFD_ALLOW_SEALING,
        )
        .expect("Failed to create anonymous file");
        owned_fd.into_raw_fd()
    }

    #[cfg(target_os = "macos")]
    fn unique_name() -> CString {
        let mut rng = rand::thread_rng();
        let random: u64 = rng.gen();
        let name_str = format!("/shm_{random}");
        return CString::new(name_str.as_str()).expect("CString::new failed");
    }

    #[cfg(target_os = "macos")]
    unsafe fn create_shm_segment() -> RawFd {
        let name = Self::unique_name();
        let fd = shm_open(name.as_ptr(), libc::O_RDWR | libc::O_CREAT, 0o666);
        if fd < 0 {
            panic!("Failed to open shared memory object");
        }
        shm_unlink(name.as_ptr());
        fd
    }
}

impl PartialEq for ShmSegment {
    fn eq(&self, rhs: &ShmSegment) -> bool {
        self.size == rhs.size && self.fd.as_raw_fd() == rhs.fd.as_raw_fd()
    }
}

impl Eq for ShmSegment {}

impl std::hash::Hash for ShmSegment {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        state.write_i32(self.fd.as_raw_fd());
        state.write_usize(self.size)
    }
}

impl Drop for ShmSegment {
    fn drop(&mut self) {
        match Arc::get_mut(&mut self.addr) {
            Some(addr) => unsafe {
                libc::munmap(*addr as *mut c_void, self.size);
            },
            None => (),
        }
    }
}

impl IsoxTermSerialize for ShmSegment {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        ctx.fds.push(self.fd.clone());
        ctx.data.extend_from_slice(&self.size.to_be_bytes());
    }
}

impl IsoxTermDeserialize for ShmSegment {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> ShmSegment {
        let (bytes, rest) = ctx.data.split_at(std::mem::size_of::<usize>());
        ctx.data = rest;

        let size = usize::from_be_bytes(bytes.try_into().unwrap());
        let fd = ctx.fds.remove(0);
        let addr = unsafe {
            let result = libc::mmap(
                ptr::null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                fd.as_raw_fd(),
                0,
            );

            if result == libc::MAP_FAILED {
                let err = std::io::Error::last_os_error();
                eprintln!("{} mmap failed: {}", std::process::id(), err);
                panic!("mmap failed with error: {}", err);
            }

            result
        };

        ShmSegment {
            fd,
            size,
            addr: Arc::new(addr as usize),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TermValue {
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    Pid(usize),
    Map(HashMap<Arc<Term>, Arc<Term>>),
    List(Vec<Arc<Term>>),
    Shm(ShmSegment),
    Atom(String),
    Tuple(Vec<Arc<Term>>),
    Resource((u64, RawPointer<c_void>)),
    ResourceRef((u64, RawPointer<c_void>)),
    SubBinary(Arc<Term>, usize, usize),
}

impl PartialEq for TermValue {
    fn eq(&self, rhs: &TermValue) -> bool {
        match (self, rhs) {
            (TermValue::Bool(l), TermValue::Bool(r)) => l == r,
            (TermValue::Int(l), TermValue::Int(r)) => l == r,
            (TermValue::Float(l), TermValue::Float(r)) => l == r,
            (TermValue::String(l), TermValue::String(r)) => l == r,
            (TermValue::Pid(l), TermValue::Pid(r)) => l == r,
            (TermValue::Map(l), TermValue::Map(r)) => l == r,
            (TermValue::List(l), TermValue::List(r)) => l == r,
            (TermValue::Shm(l), TermValue::Shm(r)) => l == r,
            (TermValue::Atom(l), TermValue::Atom(r)) => l == r,
            (TermValue::Tuple(l), TermValue::Tuple(r)) => l == r,
            (TermValue::Resource(l), TermValue::Resource(r)) => l == r,
            (TermValue::ResourceRef(l), TermValue::ResourceRef(r)) => l == r,
            (TermValue::SubBinary(b_l, s_l, l_l), TermValue::SubBinary(b_r, s_r, l_r)) => {
                b_l == b_r && s_l == s_r && l_l == l_r
            }
            (_, _) => false,
        }
    }
}
impl Eq for TermValue {}

impl std::hash::Hash for TermValue {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        match self {
            TermValue::Bool(x) => x.hash(state),
            TermValue::Int(x) => x.hash(state),
            TermValue::Float(x) => {
                let x_str = format!("{}", x);
                x_str.hash(state)
            }
            TermValue::String(x) => x.hash(state),
            TermValue::Pid(x) => x.hash(state),
            TermValue::Map(x) => {
                state.write_usize(x.len());
                for (key, value) in x {
                    key.hash(state);
                    value.hash(state);
                }
            }
            TermValue::List(x) => x.hash(state),
            TermValue::Shm(x) => x.hash(state),
            TermValue::Atom(x) => x.hash(state),
            TermValue::Tuple(x) => x.hash(state),
            TermValue::Resource((i, p)) => {
                i.hash(state);
                p.hash(state)
            }
            TermValue::ResourceRef((i, p)) => {
                i.hash(state);
                p.hash(state)
            }
            TermValue::SubBinary(b, s, l) => {
                b.hash(state);
                s.hash(state);
                l.hash(state);
            }
        }
        state.finish();
    }
}

impl IsoxTermSerialize for TermValue {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        match self {
            TermValue::Bool(i) => {
                ctx.data.push(Tags::BoolTag as u8);
                i.isox_term_serialize(ctx);
            }
            TermValue::Int(i) => {
                ctx.data.push(Tags::IntTag as u8);
                i.isox_term_serialize(ctx);
            }
            TermValue::Float(f) => {
                ctx.data.push(Tags::FloatTag as u8);
                f.isox_term_serialize(ctx);
            }
            TermValue::String(s) => {
                ctx.data.push(Tags::StringTag as u8);
                s.isox_term_serialize(ctx);
            }
            TermValue::Pid(s) => {
                ctx.data.push(Tags::PidTag as u8);
                s.isox_term_serialize(ctx);
            }
            TermValue::Map(m) => {
                ctx.data.push(Tags::MapTag as u8);
                m.isox_term_serialize(ctx);
            }
            TermValue::List(l) => {
                ctx.data.push(Tags::ListTag as u8);
                l.isox_term_serialize(ctx);
            }
            TermValue::Shm(shm) => {
                ctx.data.push(Tags::ShmTag as u8);
                shm.isox_term_serialize(ctx);
            }
            TermValue::Atom(a) => {
                ctx.data.push(Tags::AtomTag as u8);
                a.isox_term_serialize(ctx);
            }
            TermValue::Tuple(t) => {
                ctx.data.push(Tags::TupleTag as u8);
                t.isox_term_serialize(ctx);
            }
            TermValue::Resource((i, p)) => {
                ctx.data.push(Tags::ResourceTag as u8);
                i.isox_term_serialize(ctx);
                p.isox_term_serialize(ctx);
            }
            TermValue::ResourceRef((i, p)) => {
                ctx.data.push(Tags::ResourceRefTag as u8);
                i.isox_term_serialize(ctx);
                p.isox_term_serialize(ctx);
            }
            TermValue::SubBinary(b, s, l) => {
                ctx.data.push(Tags::SubBinaryTag as u8);
                b.isox_term_serialize(ctx);
                s.isox_term_serialize(ctx);
                l.isox_term_serialize(ctx);
            }
        }
    }
}

impl IsoxTermDeserialize for TermValue {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> TermValue {
        if ctx.data.is_empty() {
            panic!("Data is empty");
        }

        let type_id = ctx.data[0];
        ctx.data = &ctx.data[1..];
        match Tags::from(type_id) {
            Tags::BoolTag => TermValue::Bool(bool::isox_term_deserialize(ctx)),
            Tags::IntTag => TermValue::Int(i64::isox_term_deserialize(ctx)),
            Tags::FloatTag => TermValue::Float(f64::isox_term_deserialize(ctx)),
            Tags::StringTag => TermValue::String(String::isox_term_deserialize(ctx)),
            Tags::PidTag => TermValue::Pid(usize::isox_term_deserialize(ctx)),
            Tags::MapTag => {
                TermValue::Map(HashMap::<Arc<Term>, Arc<Term>>::isox_term_deserialize(ctx))
            }
            Tags::ListTag => TermValue::List(Vec::<Arc<Term>>::isox_term_deserialize(ctx)),
            Tags::ShmTag => TermValue::Shm(ShmSegment::isox_term_deserialize(ctx)),
            Tags::AtomTag => TermValue::Atom(String::isox_term_deserialize(ctx)),
            Tags::TupleTag => TermValue::Tuple(Vec::<Arc<Term>>::isox_term_deserialize(ctx)),
            Tags::ResourceTag => TermValue::Resource((
                u64::isox_term_deserialize(ctx),
                RawPointer::isox_term_deserialize(ctx),
            )),
            Tags::ResourceRefTag => TermValue::ResourceRef((
                u64::isox_term_deserialize(ctx),
                RawPointer::isox_term_deserialize(ctx),
            )),
            Tags::SubBinaryTag => TermValue::SubBinary(
                Arc::isox_term_deserialize(ctx),
                usize::isox_term_deserialize(ctx),
                usize::isox_term_deserialize(ctx),
            ),
        }
    }
}

#[repr(C)]
pub struct ResourceRefData {
    pub resource_type_id: u64,
    pub obj: *const c_void,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    pub value: TermValue,
}

impl IsoxTermSerialize for Term {
    fn isox_term_serialize(&self, ctx: &mut IsoxTermSerializationContext) {
        self.value.isox_term_serialize(ctx)
    }
}

impl IsoxTermDeserialize for Term {
    fn isox_term_deserialize(ctx: &mut IsoxTermDeserializationContext) -> Term {
        Term {
            value: TermValue::isox_term_deserialize(ctx),
        }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum Tags {
    IntTag = 1,
    FloatTag = 2,
    StringTag = 3,
    PidTag = 4,
    MapTag = 5,
    ListTag = 6,
    ShmTag = 7,
    AtomTag = 8,
    TupleTag = 9,
    ResourceTag = 10,
    ResourceRefTag = 11,
    BoolTag = 12,
    SubBinaryTag = 13,
}

impl Tags {
    fn from(value: u8) -> Self {
        match value {
            1 => Tags::IntTag,
            2 => Tags::FloatTag,
            3 => Tags::StringTag,
            4 => Tags::PidTag,
            5 => Tags::MapTag,
            6 => Tags::ListTag,
            7 => Tags::ShmTag,
            8 => Tags::AtomTag,
            9 => Tags::TupleTag,
            10 => Tags::ResourceTag,
            11 => Tags::ResourceRefTag,
            12 => Tags::BoolTag,
            13 => Tags::SubBinaryTag,
            _ => panic!("Unknown plugin term tag: {}", value),
        }
    }
}

pub struct CommsSocket {
    pub socket: OwnedFd,
}

// TODO - the same as in oxidized/id3as-rustler/src/resources.rs, but nothing to do wth rustler - make a new utils crate?
#[macro_export]
macro_rules! mutex_resource {
    ($T:ty, $W:ident) => {
        pub struct $W(std::sync::Mutex<$T>);

        impl From<$T> for $W {
            fn from(resource: $T) -> Self {
                Self::new(resource)
            }
        }

        impl $W {
            pub fn new(resource: $T) -> Self {
                Self(std::sync::Mutex::new(resource))
            }

            pub fn lock(&self) -> std::sync::MutexGuard<$T> {
                match self.0.lock() {
                    Ok(x) => x,
                    Err(_) => panic!("arse"),
                } //.expect("the resource mutex has been poisoned")
            }
        }
    };
}
mutex_resource!(CommsSocket, GuardedCommsSocket);

pub fn send_message(
    guarded_socket: &GuardedCommsSocket,
    ctx: IsoxTermSerializationContext,
) -> Result<(), Errno> {
    let comms_socket = guarded_socket.lock();
    let data_len = (ctx.data.len() as u32).to_be_bytes();
    let num_fds = (ctx.fds.len() as u32).to_be_bytes();

    // We send an 8 byte control message with the length of the data and
    // number of file-descriptors
    let mut first_msg = [0u8; 8];
    first_msg[..4].copy_from_slice(&data_len);
    first_msg[4..].copy_from_slice(&num_fds);

    sendmsg(
        comms_socket.socket.as_raw_fd(),
        &[IoSlice::new(&first_msg)],
        &[],
        MsgFlags::empty(),
        None::<&UnixAddr>,
    )?;

    let fd = comms_socket.socket.as_raw_fd();
    let mut data_offset = 0;
    let mut fds_offset = 0;
    let data = &ctx.data;
    let fds = &ctx.fds;
    let data_len = data.len();
    let fds_len = fds.len();

    while data_offset < data_len || fds_offset < fds.len() {
        let end_data = (data_offset + CHUNK_SIZE).min(data_len);
        let data_chunk = &data[data_offset..end_data];

        let end_fds = (fds_offset + MAX_FDS_PER_CHUNK).min(fds_len);
        let fds_chunk = &fds[fds_offset..end_fds];

        let iov = if data_chunk.is_empty() {
            [IoSlice::new(&NOOP_TAG)]
        } else {
            [IoSlice::new(data_chunk)]
        };

        let these_fds: Vec<RawFd>;
        let mut cmsgs = Vec::new();
        let cmsgs_to_send = if fds_chunk.is_empty() {
            &[] as &[ControlMessage<'_>]
        } else {
            these_fds = fds_chunk.iter().map(|rc_fd| rc_fd.as_raw_fd()).collect();
            cmsgs.clear();
            cmsgs.push(ControlMessage::ScmRights(&these_fds));
            &cmsgs
        };

        _ = loop {
            match sendmsg(
                fd,
                &iov,
                cmsgs_to_send,
                MsgFlags::empty(),
                None::<&UnixAddr>,
            ) {
                Ok(_) => break Ok(()),
                Err(nix::errno::Errno::EAGAIN | nix::errno::Errno::ENOBUFS) => {
                    sleep(Duration::from_micros(1000000));
                    continue;
                }
                Err(e) => {
                    eprintln!("BARF {:?}", e);
                    break Err(e);
                }
            }
        };

        data_offset = end_data;
        fds_offset = end_fds;
    }

    Ok(())
}

pub struct ReadMessageContext<'a> {
    socket: &'a OwnedFd,
    awaiting_header: bool,
    next_buffer_size: usize,
    next_num_fds: usize,
    payload_size: usize,
    num_fds: usize,
    received_data: Vec<u8>,
    received_fds: Vec<Arc<OwnedFd>>,
}

pub enum ReadMessageResult {
    WouldBlock,
    Continue,
    Error(Error),
    Ok((Vec<u8>, Vec<Arc<OwnedFd>>)),
}

impl<'a> ReadMessageContext<'a> {
    pub fn new(socket: &'a OwnedFd) -> ReadMessageContext<'a> {
        ReadMessageContext {
            socket,
            awaiting_header: true,
            next_buffer_size: 8,
            next_num_fds: 0,
            payload_size: 0,
            num_fds: 0,
            received_data: Vec::new(),
            received_fds: Vec::new(),
        }
    }

    pub fn read_message(&mut self) -> ReadMessageResult {
        match recv_message(&self.socket, self.next_buffer_size, self.next_num_fds) {
            Err(err) if err.kind() == ErrorKind::WouldBlock => ReadMessageResult::WouldBlock,
            Err(err) => ReadMessageResult::Error(err),
            Ok((data, fds)) => {
                // We have a message
                if self.awaiting_header {
                    // If we were waiting on the header message then we now have it,
                    //  parse it and return continue to wait for the next message(s)
                    self.payload_size = BigEndian::read_u32(&data[0..4]) as usize;
                    self.num_fds = BigEndian::read_u32(&data[4..8]) as usize;
                    self.received_data.clear();
                    self.received_fds.clear();

                    self.next_buffer_size = self.payload_size.min(CHUNK_SIZE);
                    self.next_num_fds = if self.num_fds > 0 {
                        self.num_fds.min(MAX_FDS_PER_CHUNK)
                    } else {
                        0
                    };
                    self.awaiting_header = false;
                    ReadMessageResult::Continue
                } else {
                    // We have the data
                    if self.received_data.len() < self.payload_size {
                        // Still 'real' data - if there are many fds, then we might end up with packets just to transfer
                        // those without any real data in them
                        self.received_data.extend_from_slice(&data);
                    }
                    self.received_fds.extend(fds);

                    if self.received_data.len() == self.payload_size
                        && self.received_fds.len() == self.num_fds
                    {
                        let data_out = std::mem::take(&mut self.received_data);
                        let fds_out = std::mem::take(&mut self.received_fds);

                        self.awaiting_header = true;
                        self.next_buffer_size = 8;
                        self.next_num_fds = 0;
                        self.payload_size = 0;

                        ReadMessageResult::Ok((data_out, fds_out))
                    } else {
                        if self.received_data.len() == self.payload_size {
                            self.next_buffer_size = NOOP_TAG.len();
                        } else {
                            self.next_buffer_size =
                                (self.payload_size - self.received_data.len()).min(CHUNK_SIZE);
                        }
                        if self.received_fds.len() == self.num_fds {
                            self.next_num_fds = 0;
                        } else {
                            self.next_num_fds =
                                (self.num_fds - self.received_fds.len()).min(MAX_FDS_PER_CHUNK);
                        }
                        ReadMessageResult::Continue
                    }
                }
            }
        }
    }
}

#[cfg(target_os = "linux")]
fn recv_flags() -> MsgFlags {
    MsgFlags::MSG_CMSG_CLOEXEC
}

#[cfg(target_os = "macos")]
fn recv_flags() -> MsgFlags {
    MsgFlags::empty()
}

fn recv_message(
    socket: &OwnedFd,
    data_size: usize,
    num_fds: usize,
) -> Result<(Vec<u8>, Vec<Arc<OwnedFd>>), Error> {
    let mut buf = vec![0u8; data_size];
    let mut iov = [std::io::IoSliceMut::new(&mut buf)];
    // would be nice to not have an unsafe here, but whatever...
    let mut cmsgspace = vec![
        0u8;
        unsafe { nix::libc::CMSG_SPACE(std::mem::size_of::<RawFd>() as u32 * num_fds as u32) }
            as usize
    ];

    let result: nix::Result<RecvMsg<'_, '_, UnixAddr>> = recvmsg(
        socket.as_raw_fd(),
        &mut iov,
        if num_fds == 0 {
            None
        } else {
            Some(&mut cmsgspace)
        },
        recv_flags(),
    );

    match result {
        Err(err) => Err(err.into()),
        Ok(msg) => {
            let cmsgs_count = msg.cmsgs().count();

            if msg.bytes == 0 && cmsgs_count == 0 {
                Err(ErrorKind::NotConnected.into())
            } else {
                let mut fds = Vec::new();
                for cmsg in msg.cmsgs() {
                    if let ControlMessageOwned::ScmRights(received_fds) = cmsg {
                        for raw_fd in received_fds {
                            // Only one from_raw_fd per fd
                            fds.push(Arc::new(unsafe { OwnedFd::from_raw_fd(raw_fd) }));
                        }
                    }
                }
                // let fds: Vec<Arc<OwnedFd>> = msg
                //     .cmsgs()
                //     .filter_map(|cmsg| {
                //         if let nix::sys::socket::ControlMessageOwned::ScmRights(fds) = cmsg {
                //             Some(fds)
                //         } else {
                //             None
                //         }
                //     })
                //     .flatten()
                //     .map(|fd| Arc::new(OwnedFd::from(fd)))
                //     // .map(|fd| Arc::new(unsafe { OwnedFd::from_raw_fd(fd) }))
                //     .collect();

                Ok((buf, fds))
            }
        }
    }
}

pub fn append_line_to_file(line: &String) -> std::io::Result<()> {
    let path = String::from("/tmp/trace.out");
    let mut file = OpenOptions::new()
        .write(true) // Enable writing
        .append(true) // Open file in append mode
        .create(true) // Create file if it doesn't exist
        .open(path)?;

    writeln!(file, "{}", line)?; // Use `writeln!` to automatically add a newline at the end of the line

    Ok(())
}

pub fn set_non_blocking(fd: RawFd) {
    let flags = fcntl(fd, FcntlArg::F_GETFL).expect("Should get flags");
    let new_flags = OFlag::from_bits_truncate(flags) | OFlag::O_NONBLOCK;
    fcntl(fd, FcntlArg::F_SETFL(new_flags)).expect("Should set flags");
}
