use std::{fs::read_to_string, io::stderr};

use lrpar::Span;
use rboehm::Gc;
use termion::{is_tty, style};

use crate::vm::{
    core::VM,
    objects::{Class, Method, ObjType, String_},
    val::Val,
};

#[derive(Debug)]
pub struct VMError {
    pub kind: VMErrorKind,
    /// The callstack (in reverse order) of (Class, Span) pairs.
    pub backtrace: Vec<(Gc<Method>, Span)>,
}

impl VMError {
    pub fn new(vm: &VM, kind: VMErrorKind) -> Box<Self> {
        let backtrace = Vec::with_capacity(vm.frames_len());
        Box::new(VMError { kind, backtrace })
    }

    pub fn console_print(&self, vm: &VM) {
        eprintln!("Traceback (most recent call at bottom):");
        for (method, span) in self.backtrace.iter().rev() {
            let cls_val = method.class();
            let cls: &Class = cls_val.downcast(vm).unwrap();
            let cls_path = cls.path.to_str().unwrap_or("<non-UTF8 filename>");

            if let Ok(d) = read_to_string(&cls.path) {
                let newlines = self.newlines(&d);
                let (start_line, start_col) = self.line_col(&newlines, span.start());
                let (end_line, end_col) = self.line_col(&newlines, span.end());
                eprintln!(
                    "  File {}, line {}, column {}:",
                    cls_path, start_line, start_col
                );
                let line = &d[newlines[start_line - 2]..newlines[start_line - 1]].trim_end();
                if is_tty(&stderr()) {
                    if start_line == end_line {
                        eprintln!(
                            "{}{}{}{}{}{}",
                            &line[..start_col],
                            style::Bold,
                            style::Underline,
                            &line[start_col..end_col],
                            style::Reset,
                            &line[end_col..]
                        );
                    } else {
                        eprintln!(
                            "{}{}{}{}{}",
                            &line[..start_col],
                            style::Bold,
                            style::Underline,
                            &line[start_col..],
                            style::Reset
                        );
                        for i in start_line..=end_line - 2 {
                            let line = if i == newlines.len() {
                                &d[newlines[i - 1]..]
                            } else {
                                &d[newlines[i - 1]..newlines[i]]
                            }
                            .trim_end();
                            let spaces = line.chars().take_while(|c| *c == ' ').count();
                            eprintln!(
                                "  {}{}{}{}{}",
                                " ".repeat(spaces),
                                style::Bold,
                                style::Underline,
                                &line[spaces..],
                                style::Reset
                            );
                        }
                        let line = &d[newlines[end_line - 2]..newlines[end_line - 1]].trim_end();
                        let spaces = line.chars().take_while(|c| *c == ' ').count();
                        eprintln!(
                            "  {}{}{}{}{}{}",
                            " ".repeat(spaces),
                            style::Bold,
                            style::Underline,
                            &line[spaces..end_col],
                            style::Reset,
                            &line[end_col..]
                        );
                    }
                } else {
                    for i in start_line - 1..end_line {
                        let line = if i == newlines.len() {
                            &d[newlines[i - 1]..]
                        } else {
                            &d[newlines[i - 1]..newlines[i]]
                        };
                        eprintln!("  {}", line.trim_end());
                    }
                }
            } else {
                eprintln!("File {}:", cls_path);
            }
        }
        match self.kind.to_string(vm) {
            Ok(s) => eprintln!("{}.", s),
            Err(_) => {
                // We could do something more clever here, but it's not clear that it's worth it.
                eprintln!("<Fatal error when running error handler>")
            }
        }
    }

    fn newlines(&self, d: &str) -> Vec<usize> {
        d.char_indices()
            .filter(|(_, c)| *c == '\n')
            .map(|(i, _)| i + 1)
            .collect()
    }

    fn line_col(&self, newlines: &[usize], i: usize) -> (usize, usize) {
        if newlines.is_empty() || i < newlines[0] {
            return (1, i);
        }

        for j in 0..newlines.len() - 1 {
            if newlines[j + 1] > i {
                return (j + 2, i - newlines[j]);
            }
        }
        (newlines.len() + 1, i - newlines[newlines.len() - 1])
    }
}

#[derive(Debug, PartialEq)]
pub enum VMErrorKind {
    /// We expected a Rust type `expected` but at run-time got a Rust type `got`.
    BuiltinTypeError {
        expected: ObjType,
        got: ObjType,
    },
    /// A value which can't be represented in an `f64`.
    CantRepresentAsDouble,
    /// A value which can't be represented in an `isize`.
    CantRepresentAsIsize,
    /// A value which can't be represented in an `usize`.
    CantRepresentAsUsize,
    DivisionByZero,
    /// A value which is mathematically undefined.
    DomainError,
    /// The VM is trying to exit.
    Exit,
    /// Tried to access an out-of-bounds element.
    IndexError {
        tried: usize,
        max: usize,
    },
    /// We expected a SOM value that is an instance of `expected_cls` but at run-time got a SOM
    /// value that is an instance of `got_cls`.
    InstanceTypeError {
        expected_cls: Val,
        got_cls: Val,
    },
    /// Tried to access a global before it being initialised.
    InvalidSymbol,
    /// Tried to do a shl or shr with a value below zero.
    NegativeShift,
    /// A specialised version of TypeError, because SOM has more than one number type (and casts
    /// between them as necessary) so the `expected` field of `TypeError` doesn't quite work.
    NotANumber {
        got: ObjType,
    },
    /// Something went wrong when trying to execute a primitive.
    PrimitiveError,
    /// Tried to do a shl that would overflow memory and/or not fit in the required integer size.
    ShiftTooBig,
    /// An unknown global.
    UnknownGlobal(String),
    /// An unknown method.
    UnknownMethod(String),
}

impl VMErrorKind {
    fn to_string(&self, vm: &VM) -> Result<String, Box<VMError>> {
        match self {
            VMErrorKind::BuiltinTypeError { expected, got } => Ok(format!(
                "Expected object of type '{}' but got type '{}'",
                expected.as_str(),
                got.as_str()
            )),
            VMErrorKind::CantRepresentAsDouble => Ok("Can't represent as double".to_owned()),
            VMErrorKind::CantRepresentAsIsize => {
                Ok("Can't represent as signed machine integer".to_owned())
            }
            VMErrorKind::CantRepresentAsUsize => {
                Ok("Can't represent as unsigned machine integer".to_owned())
            }
            VMErrorKind::DivisionByZero => Ok("Division by zero".to_owned()),
            VMErrorKind::DomainError => Ok("Domain error".to_owned()),
            VMErrorKind::Exit => Ok("Exit".to_owned()),
            VMErrorKind::IndexError { tried, max } => Ok(format!(
                "Index {} not valid for array of length {}",
                tried, max
            )),
            VMErrorKind::InstanceTypeError {
                expected_cls,
                got_cls,
            } => {
                let expected_name_val = expected_cls.downcast::<Class>(vm)?.name;
                let got_name_val = got_cls.downcast::<Class>(vm)?.name;
                let expected_name: &String_ = expected_name_val.downcast(vm)?;
                let got_name: &String_ = got_name_val.downcast(vm)?;
                Ok(format!(
                    "Expected instance of '{}' but got instance of '{}'",
                    expected_name.as_str(),
                    got_name.as_str()
                ))
            }
            VMErrorKind::InvalidSymbol => Ok("Invalid symbol".to_owned()),
            VMErrorKind::NegativeShift => Ok("Negative shift".to_owned()),
            VMErrorKind::NotANumber { got } => Ok(format!(
                "Expected a numeric type but got type '{}'",
                got.as_str()
            )),
            VMErrorKind::PrimitiveError => Ok("Primitive Error".to_owned()),
            VMErrorKind::ShiftTooBig => Ok("Shift too big".to_owned()),
            VMErrorKind::UnknownGlobal(name) => Ok(format!("Unknown global '{}'", name)),
            VMErrorKind::UnknownMethod(name) => Ok(format!("Unknown method '{}'", name)),
        }
    }
}
