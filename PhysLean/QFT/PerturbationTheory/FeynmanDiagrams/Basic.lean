/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
/-!
# Feynman diagrams

Feynman diagrams form a type into which permissible Wick contractions
embed.

A permissible Wick contraction is one which does not contribute zero to
the vacuum expectation value.

Feynman diagrams are based on multisets of `FieldOp`. This should be contrasted
with Wick contractions which are based on lists of `FieldOp`.

In particular a Feynman diagram is a partition of a Multiset into
disjoint pairs.

## Note

This directory is currently a work in progress.
(Contact JTS before working in this directory.)

-/
