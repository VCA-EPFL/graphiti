/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public meta import Lean

public meta section

register_simp_attr dmod
register_simp_attr drunfold
register_simp_attr drdecide
register_simp_attr drnat

-- General reduction of datastructures such as AssocLists.
register_simp_attr drcompute

-- Reduction of top-level rewrite definitions.
register_simp_attr drunfold_defs

-- Reduction of components, so it should include all functions that are used to construct StringModules from NatModules.
register_simp_attr drcomponents

-- Common options for module reduction, which will be passed to all simp and dsimp calls.
register_simp_attr drcommon

register_simp_attr drnorm

-- Reduce logical proposition
register_simp_attr drlogic

-- Reduce the environment
register_simp_attr drenv
