//! Core MIR abstract syntax types for `anneal-mir`.

/// Integer scalar width and signedness.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl IntTy {
    /// Size in bytes on a 64-bit target.
    pub fn byte_size(self) -> usize {
        match self {
            IntTy::Isize => 8,
            IntTy::I8 => 1,
            IntTy::I16 => 2,
            IntTy::I32 => 4,
            IntTy::I64 => 8,
            IntTy::I128 => 16,
        }
    }
}

/// Unsigned integer scalar width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl UintTy {
    /// Size in bytes on a 64-bit target.
    pub fn byte_size(self) -> usize {
        match self {
            UintTy::Usize => 8,
            UintTy::U8 => 1,
            UintTy::U16 => 2,
            UintTy::U32 => 4,
            UintTy::U64 => 8,
            UintTy::U128 => 16,
        }
    }
}

/// Mutability qualifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mutability {
    Not,
    Mut,
}

/// MIR type representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Bool,
    Int(IntTy),
    Uint(UintTy),
    RawPtr(Box<Ty>, Mutability),
    Ref(Box<Ty>, Mutability),
    Array(Box<Ty>, usize),
    Tuple(Vec<Ty>),
    Never,
}

impl Ty {
    /// Returns true if this type is an integer type (signed or unsigned).
    pub fn is_integral(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Uint(_))
    }

    /// Returns true if this type is a raw pointer.
    pub fn is_raw_ptr(&self) -> bool {
        matches!(self, Ty::RawPtr(_, _))
    }

    /// Returns true if this type is a reference.
    pub fn is_ref(&self) -> bool {
        matches!(self, Ty::Ref(_, _))
    }

    /// Returns true if this type is a pointer (raw pointer or reference).
    pub fn is_any_ptr(&self) -> bool {
        self.is_raw_ptr() || self.is_ref()
    }

    /// Size in bytes on a 64-bit target architecture.
    pub fn byte_size(&self) -> usize {
        match self {
            Ty::Bool => 1,
            Ty::Int(it) => it.byte_size(),
            Ty::Uint(ut) => ut.byte_size(),
            Ty::RawPtr(_, _) | Ty::Ref(_, _) => 8,
            Ty::Array(elem, count) => elem.byte_size() * count,
            Ty::Tuple(fields) => fields.iter().map(|f| f.byte_size()).sum(),
            Ty::Never => 0,
        }
    }
}

/// Local variable index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Local(pub usize);

/// Projection element inside a place expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ProjectionElem {
    Deref,
    Field(usize, Ty),
    Index(Local),
    ConstantIndex { offset: u64, min_length: u64, from_end: bool },
    Subslice { from: u64, to: u64, from_end: bool },
    Downcast(usize),
}

/// A place expression: base local and sequence of projections.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<ProjectionElem>,
}

impl Place {
    pub fn from_local(local: usize) -> Self {
        Place { local: Local(local), projection: Vec::new() }
    }
}

/// Pointer provenance representation matching Anneal/MiniRust provenance model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Provenance {
    pub alloc_id: u64,
    pub tag: u64,
}

/// Machine pointer value: address (or offset) paired with optional provenance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PointerValue {
    pub addr: u64,
    pub provenance: Option<Provenance>,
}

impl PointerValue {
    pub fn without_provenance(addr: u64) -> Self {
        PointerValue { addr, provenance: None }
    }

    pub fn with_provenance(addr: u64, alloc_id: u64, tag: u64) -> Self {
        PointerValue {
            addr,
            provenance: Some(Provenance { alloc_id, tag }),
        }
    }
}

/// Constant value in MIR operands.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constant {
    Int(u128, Ty),
    Bool(bool),
    Ptr(PointerValue, Ty),
}

/// Operand in MIR expressions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

/// Cast flavor in `Rvalue::Cast`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastKind {
    /// Exposing pointer-to-address cast (`*const T as usize`, `*mut T as u64`).
    PointerExposeProvenance,
    /// Provenance-capturing address-to-pointer cast (`usize as *const T`).
    PointerWithExposedProvenance,
    /// Direct integer numeric conversion (`u8 as u32`, `i64 as i32`).
    IntToInt,
    /// Raw pointer type change (`*const u8 as *const i32`).
    PtrToPtr,
    /// Bitwise reinterpretation.
    Transmute,
}

/// Binary operation flavor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
}

/// Unary operation flavor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

/// Right-hand side rvalue expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Rvalue {
    Use(Operand),
    Cast(CastKind, Operand, Ty),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
}

/// MIR statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    Assign(Place, Rvalue),
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}

/// Basic block consisting of statements and a terminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub is_cleanup: bool,
}

/// Captured MIR body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub local_decls: Vec<Ty>,
    pub basic_blocks: Vec<BasicBlockData>,
}
