use lrpar::Span;

#[derive(Debug)]
pub struct Class {
    pub name: Span,
    pub supername: Option<Span>,
    pub inst_vars: Vec<Span>,
    pub methods: Vec<Method>,
}

#[derive(Debug)]
pub struct Method {
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
        id: Span,
        expr: Box<Expr>,
    },
    BinaryMsg {
        lhs: Box<Expr>,
        op: Span,
        rhs: Box<Expr>,
    },
    Block {
        params: Vec<Span>,
        vars: Vec<Span>,
        exprs: Vec<Expr>,
    },
    Double {
        is_negative: bool,
        val: Span,
    },
    Int {
        is_negative: bool,
        val: Span,
    },
    KeywordMsg {
        receiver: Box<Expr>,
        msglist: Vec<(Span, Expr)>,
    },
    UnaryMsg {
        receiver: Box<Expr>,
        ids: Vec<Span>,
    },
    Return(Box<Expr>),
    String(Span),
    Symbol(Span),
    VarLookup(Span),
}
