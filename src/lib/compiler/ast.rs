use lrpar::Span;

#[derive(Debug)]
pub struct Class {
    pub name: Span,
    pub supername: Option<Span>,
    pub inst_vars: Vec<Span>,
    pub methods: Vec<Method>,
    pub class_inst_vars: Vec<Span>,
    pub class_methods: Vec<Method>,
}

#[derive(Debug)]
pub struct Method {
    pub span: Span,
    pub name: MethodName,
    pub body: MethodBody,
}

#[derive(Debug)]
pub enum MethodName {
    BinaryOp(Span, Option<Span>),
    Id(Span),
    Keywords(Vec<(Span, Span)>),
}

#[derive(Debug)]
pub enum MethodBody {
    Primitive,
    Body { vars: Vec<Span>, exprs: Vec<Expr> },
}

#[derive(Debug)]
pub enum Expr {
    Assign {
        span: Span,
        id: Span,
        expr: Box<Expr>,
    },
    BinaryMsg {
        span: Span,
        lhs: Box<Expr>,
        op: Span,
        rhs: Box<Expr>,
    },
    Block {
        span: Span,
        params: Vec<Span>,
        vars: Vec<Span>,
        exprs: Vec<Expr>,
    },
    Double {
        span: Span,
        is_negative: bool,
        val: Span,
    },
    Int {
        span: Span,
        is_negative: bool,
        val: Span,
    },
    KeywordMsg {
        span: Span,
        receiver: Box<Expr>,
        msglist: Vec<(Span, Expr)>,
    },
    UnaryMsg {
        span: Span,
        receiver: Box<Expr>,
        ids: Vec<Span>,
    },
    Return {
        span: Span,
        expr: Box<Expr>,
    },
    String(Span),
    Symbol(Span),
    VarLookup(Span),
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Assign { span, .. } => *span,
            Expr::BinaryMsg { span, .. } => *span,
            Expr::Block { span, .. } => *span,
            Expr::Double { span, .. } => *span,
            Expr::Int { span, .. } => *span,
            Expr::KeywordMsg { span, .. } => *span,
            Expr::UnaryMsg { span, .. } => *span,
            Expr::Return { span, .. } => *span,
            Expr::String(span) => *span,
            Expr::Symbol(span) => *span,
            Expr::VarLookup(span) => *span,
        }
    }
}
