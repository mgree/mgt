use crate::syntax::*;

impl SourceUOp {
    /// Returns the sole possibility for a unary operation.
    ///
    /// TODO with overloaded ones, we need UOpSignature, like below
    pub fn explicit(&self) -> ExplicitUOp {
        match self {
            SourceUOp::Negate => ExplicitUOp::Negate,
            SourceUOp::Not => ExplicitUOp::Not,
            SourceUOp::Is(g) => ExplicitUOp::Is(*g),
        }
    }
}

/// Different binary operation signatures.
pub enum BOpSignature {
    /// Used when any consistent type is okay. Only for non-overloaded operations.
    Simple(ExplicitBOp),
    Overloaded {
        dyn_op: ExplicitBOp,
        overloads: Vec<ExplicitBOp>,
    },
}

impl SourceBOp {
    pub fn explicit(&self) -> BOpSignature {
        match self {
            SourceBOp::Plus => BOpSignature::Overloaded {
                dyn_op: ExplicitBOp::PlusDyn,
                overloads: vec![ExplicitBOp::PlusInt, ExplicitBOp::PlusString],
            },
            SourceBOp::Equal => BOpSignature::Overloaded {
                dyn_op: ExplicitBOp::EqualDyn,
                overloads: vec![
                    ExplicitBOp::EqualBool,
                    ExplicitBOp::EqualInt,
                    ExplicitBOp::EqualString,
                ],
            },
            SourceBOp::And => BOpSignature::Simple(ExplicitBOp::And),
            SourceBOp::Or => BOpSignature::Simple(ExplicitBOp::Or),
            SourceBOp::Minus => BOpSignature::Simple(ExplicitBOp::Minus),
            SourceBOp::Times => BOpSignature::Simple(ExplicitBOp::Times),
            SourceBOp::Divide => BOpSignature::Simple(ExplicitBOp::Divide),
            SourceBOp::LessThan => BOpSignature::Simple(ExplicitBOp::LessThan),
            SourceBOp::LessThanEqual => BOpSignature::Simple(ExplicitBOp::LessThanEqual),
        }
    }
}

impl ExplicitUOp {
    pub fn signature(&self) -> (GradualType, GradualType) {
        match self {
            ExplicitUOp::Negate => (GradualType::int(), GradualType::int()),
            ExplicitUOp::Not => (GradualType::bool(), GradualType::bool()),
            ExplicitUOp::Is(_g) => (GradualType::Dyn(), GradualType::bool()),
        }
    }
}

impl ExplicitBOp {
    pub fn signature(&self) -> (GradualType, GradualType) {
        match self {
            ExplicitBOp::PlusInt => (GradualType::int(), GradualType::int()),
            ExplicitBOp::PlusString => (GradualType::string(), GradualType::string()),
            ExplicitBOp::PlusDyn => (GradualType::Dyn(), GradualType::Dyn()),
            ExplicitBOp::Minus => (GradualType::int(), GradualType::int()),
            ExplicitBOp::Times => (GradualType::int(), GradualType::int()),
            ExplicitBOp::Divide => (GradualType::int(), GradualType::int()),
            ExplicitBOp::And => (GradualType::bool(), GradualType::bool()),
            ExplicitBOp::Or => (GradualType::bool(), GradualType::bool()),
            ExplicitBOp::EqualBool => (GradualType::bool(), GradualType::bool()),
            ExplicitBOp::EqualInt => (GradualType::int(), GradualType::bool()),
            ExplicitBOp::EqualString => (GradualType::string(), GradualType::bool()),
            ExplicitBOp::EqualDyn => (GradualType::Dyn(), GradualType::bool()),
            ExplicitBOp::LessThan => (GradualType::int(), GradualType::bool()),
            ExplicitBOp::LessThanEqual => (GradualType::int(), GradualType::bool()),
            ExplicitBOp::Choice(_, _, _) => panic!("asked for signature of choice"),
        }
    }
}