// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Claims and supporting traits for multi-circuit aggregation.
//!
//! A [`Claim`] is a `(vk, statement)` pair representing the assertion that
//! `statement` holds under the inner circuit identified by `vk`. The aggregator
//! collects one claim per IVC step.
//!
//! Because different inner circuits have different statement types, statements
//! are stored as `Box<dyn Statement>` for type-erased access. The
//! [`AggregableRelation`] trait marks a
//! [`Relation`](midnight_zk_stdlib::Relation) as aggregation-compatible
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
