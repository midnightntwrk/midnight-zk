//! Claims and supporting traits for multi-circuit aggregation.
//!
//! A [`Claim`] is a `(vk, statement)` pair representing the assertion that
//! `statement` holds under the inner circuit identified by `vk`. The aggregator
//! collects one claim per IVC step.
//!
//! Because different inner circuits have different statement types, statements
//! are stored as `Box<dyn Statement>` for type-erased access. The
//! [`AggregableRelation`] trait marks a [`Relation`] as aggregation-compatible
//! and [`TypedStatement`] bridges it to the [`Statement`] trait object.

use std::fmt::Debug;

use midnight_zk_stdlib::MidnightVK;

use super::AggregableRelation;
use crate::ivc::F;

/// A claim: an inner-circuit verifying key paired with a corresponding
/// statement (public inputs).
#[derive(Clone, Debug)]
pub struct Claim {
    /// Verifying key identifying the inner circuit this claim refers to.
    pub vk: MidnightVK,
    /// The public input of the inner proof, encoded as a single field element.
    pub statement: Box<dyn Statement>,
}

/// Trait that all inner-circuit statement types must implement, enabling
/// type-erased storage in [`Claim`] via `Box<dyn Statement>`.
pub trait Statement: Debug {
    /// Encodes the statement as a single public-input field element.
    fn format_instance(&self) -> F;

    /// Clone into a boxed trait object.
    fn clone_boxed(&self) -> Box<dyn Statement>;
}

impl Clone for Box<dyn Statement> {
    fn clone(&self) -> Self {
        self.clone_boxed()
    }
}

/// Type-erased wrapper that implements [`Statement`] for any
/// [`AggregableRelation`].
#[derive(Debug, Clone)]
pub struct TypedStatement<R: AggregableRelation>(pub R::Instance);

impl<R: AggregableRelation> TypedStatement<R> {
    /// Creates a new typed statement from a relation instance.
    pub fn new(instance: R::Instance) -> Self {
        Self(instance)
    }
}

impl<R> Statement for TypedStatement<R>
where
    R: AggregableRelation + Debug + 'static,
    R::Instance: Debug + Clone,
{
    fn format_instance(&self) -> F {
        R::format_statement(&self.0)
    }

    fn clone_boxed(&self) -> Box<dyn Statement> {
        Box::new(self.clone())
    }
}
