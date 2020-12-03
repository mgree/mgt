use std::convert::TryFrom;

use ena::unify::{InPlace, UnificationTable, UnifyKey, UnifyValue};

use crate::syntax::*;

// TODO type schemes

// unification w/union-find
type Subst = UnificationTable<InPlace<TypeVariable>>;

#[derive(Debug)]
pub enum TypeError {
    TypeMismatch(GradualType, GradualType),
}

impl UnifyValue for GradualType {
    type Error = TypeError;

    fn unify_values(g1: &Self, g2: &Self) -> Result<Self, Self::Error> {
        use GradualType::*;
        use TypeError::TypeMismatch;
        match (g1, g2) {
            (Dyn(), Dyn()) => Ok(Dyn()),
            (Base(b1), Base(b2)) => {
                if b1 == b2 {
                    Ok(Base(*b1))
                } else {
                    Err(TypeMismatch(g1.clone(), g2.clone()))
                }
            }
            (Fun(g11, g12), Fun(g21, g22)) => {
                let g1 = UnifyValue::unify_values(g11.as_ref(), g21.as_ref())?;
                let g2 = UnifyValue::unify_values(g12.as_ref(), g22.as_ref())?;
                Ok(GradualType::fun(g1, g2))
            }
            (List(g1), List(g2)) => {
                let g = UnifyValue::unify_values(g1.as_ref(), g2.as_ref())?;
                Ok(GradualType::list(g))
            }
            (g, Var(_)) | (Var(_), g) => Ok(g.clone()),
            (g1, g2) => Err(TypeMismatch(g1.clone(), g2.clone())),
        }
    }
}

impl UnifyKey for TypeVariable {
    type Value = Option<GradualType>;

    fn from_index(a: u32) -> Self {
        TypeVariable(a as usize)
    }
    fn index(&self) -> u32 {
        u32::try_from(self.0).expect("couldn't fit type variable in 32 bits")
    }
    fn tag() -> &'static str {
        "TypeVariable"
    }
}

pub fn unify(subst: &mut Subst, g1: GradualType, g2: GradualType) -> Result<(), TypeError> {
    use GradualType::*;
    use TypeError::TypeMismatch;

    match (g1, g2) {
        (Dyn(), Dyn()) => Ok(()),
        (Base(b1), Base(b2)) => {
            if b1 == b2 {
                Ok(())
            } else {
                Err(TypeMismatch(Base(b1), Base(b2)))
            }
        }
        (Fun(g11, g12), Fun(g21, g22)) => {
            unify(subst, *g11, *g21)?;
            unify(subst, *g12, *g22)
        }
        (List(g1), List(g2)) => unify(subst, *g1, *g2),
        (Var(a1), Var(a2)) => {
            eprintln!(
                "unified {} ({:?}) and {} ({:?})",
                a1,
                subst.probe_value(a1),
                a2,
                subst.probe_value(a2)
            );

            if let (Some(g1), Some(g2)) = (subst.probe_value(a1), subst.probe_value(a2)) {
                unify(subst, g1, g2)?;
            }

            subst.unify_var_var(a1, a2)
        }
        (g, Var(a)) | (Var(a), g) => {
            eprintln!("unified {} ({:?}) and {}", a, subst.probe_value(a), g);
            subst.unify_var_value(a, Some(g))
        }
        (g1, g2) => Err(TypeMismatch(g1.clone(), g2.clone())),
    }
}

impl GradualType {
    pub fn substitute(&mut self, subst: &mut Subst) {
        use GradualType::*;
        match self {
            Var(a) => *self = a.substitute(subst),
            Dyn() | Base(_) => (),
            Fun(g1, g2) => {
                g1.substitute(subst);
                g2.substitute(subst);
            }
            List(g) => g.substitute(subst),
        }
    }
}

impl TypeVariable {
    pub fn substitute(self, subst: &mut Subst) -> GradualType {
        match subst.probe_value(self) {
            // avoid infinite loops
            Some(GradualType::Var(a)) if a == self => GradualType::Var(self),
            Some(mut g) => {
                g.substitute(subst);
                g
            }
            None => GradualType::Var(self),
        }
    }
}

// constraint-based approach
#[derive(Clone, Debug)]
pub enum Constraint {
    Equal {
        expected: GradualType,
        got: GradualType,
    },
    Instantiate {
        known: GradualType,
        to: GradualType,
    },
    Generalize {
        known: GradualType,
        to: GradualType,
    },
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn unify_var_base() {
        let mut subst = Subst::new();

        let u = subst.new_key(None);
        let g = GradualType::Base(BaseType::Bool);

        unify(&mut subst, GradualType::Var(u), g.clone()).expect("unified");

        assert_eq!(u.substitute(&mut subst), g);
    }

    #[test]
    fn unify_var_fun() {
        let mut subst = Subst::new();

        let u = subst.new_key(None);
        let g = GradualType::fun(
            GradualType::Base(BaseType::Bool),
            GradualType::Base(BaseType::Int),
        );

        unify(&mut subst, GradualType::Var(u), g.clone()).expect("unified");

        assert_eq!(u.substitute(&mut subst), g);
    }

    #[test]
    fn unify_fun_fun() {
        let mut subst = Subst::new();

        let u11 = subst.new_key(None);
        let u12 = subst.new_key(None);

        let u21 = subst.new_key(None);
        let u22 = subst.new_key(None);

        unify(
            &mut subst,
            GradualType::Var(u11),
            GradualType::Base(BaseType::String),
        )
        .unwrap();
        unify(
            &mut subst,
            GradualType::Var(u22),
            GradualType::Base(BaseType::Int),
        )
        .unwrap();

        unify(
            &mut subst,
            GradualType::fun(GradualType::Var(u11), GradualType::Var(u12)),
            GradualType::fun(GradualType::Var(u21), GradualType::Var(u22)),
        )
        .unwrap();
        assert_eq!(
            u11.substitute(&mut subst),
            GradualType::Base(BaseType::String)
        );
        assert_eq!(
            u21.substitute(&mut subst),
            GradualType::Base(BaseType::String)
        );
        assert_eq!(u12.substitute(&mut subst), GradualType::Base(BaseType::Int));
        assert_eq!(u22.substitute(&mut subst), GradualType::Base(BaseType::Int));
    }

    #[test]
    fn unify_fun_fun_indirect() {
        let mut subst = Subst::new();

        let u11 = subst.new_key(None);
        let u12 = subst.new_key(None);
        let u1 = subst.new_key(Some(GradualType::fun(
            GradualType::Var(u11),
            GradualType::Var(u12),
        )));
        let u21 = subst.new_key(None);
        let u22 = subst.new_key(None);
        let u2 = subst.new_key(Some(GradualType::fun(
            GradualType::Var(u21),
            GradualType::Var(u22),
        )));

        unify(
            &mut subst,
            GradualType::Var(u11),
            GradualType::Base(BaseType::String),
        )
        .unwrap();
        unify(
            &mut subst,
            GradualType::Var(u22),
            GradualType::Base(BaseType::Int),
        )
        .unwrap();

        unify(&mut subst, GradualType::Var(u1), GradualType::Var(u2)).unwrap();

        assert_eq!(
            u11.substitute(&mut subst),
            GradualType::Base(BaseType::String)
        );
        assert_eq!(
            u21.substitute(&mut subst),
            GradualType::Base(BaseType::String)
        );
        assert_eq!(u12.substitute(&mut subst), GradualType::Base(BaseType::Int));
        assert_eq!(u22.substitute(&mut subst), GradualType::Base(BaseType::Int));

        assert_eq!(
            u1.substitute(&mut subst),
            GradualType::fun(
                GradualType::Base(BaseType::String),
                GradualType::Base(BaseType::Int)
            )
        );
        assert_eq!(
            u2.substitute(&mut subst),
            GradualType::fun(
                GradualType::Base(BaseType::String),
                GradualType::Base(BaseType::Int)
            )
        );
    }
}
