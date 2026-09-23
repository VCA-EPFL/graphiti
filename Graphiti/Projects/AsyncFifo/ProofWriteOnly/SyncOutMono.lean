/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Filtered
import Graphiti.Projects.AsyncFifo.components.level3.Contracts
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage

/-! # The synchroniser stage's output only grows

`syncOut` is monotone in all three of its input streams: what the stage reported for shorter
inputs is a prefix of what it reports for longer ones. -/

namespace Graphiti.AsyncFifo.Timed

variable {n : Nat}

theorem syncInp_congr {lat su : Nat} {clk clk' : List Bool} {d d' : List (BitVec (n+1))} {orc orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : d <+: d') (h₃ : orc <+: orc') {t : Nat} (ht : t < SyncStage.syncLen lat clk d orc) :
    SyncStage.syncInp lat su clk d orc t = SyncStage.syncInp lat su clk' d' orc' t := by
  unfold SyncStage.syncLen at ht
  unfold SyncStage.syncInp
  rw [riseAt_prefix h₁ (by omega), delayed_congr h₂ (by omega), delayed_congr h₂ (by omega), h₃.getD_eq_left (by omega)]

theorem syncLen_mono {lat : Nat} {clk clk' : List Bool} {d d' : List (BitVec (n+1))} {orc orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : d <+: d') (h₃ : orc <+: orc') : SyncStage.syncLen lat clk d orc ≤ SyncStage.syncLen lat clk' d' orc' := by
  have := h₁.length_le; have := h₂.length_le; have := h₃.length_le
  unfold SyncStage.syncLen; omega

theorem syncOut_mono {lat su stl : Nat} {clk clk' : List Bool} {d d' : List (BitVec (n+1))} {orc orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : d <+: d') (h₃ : orc <+: orc') :
    SyncStage.syncOut lat su stl clk d orc <+: SyncStage.syncOut lat su stl clk' d' orc' := by
  apply timeline_mono (syncLen_mono h₁ h₂ h₃)
  intro t ht
  have hrun : SyncStage.syncRun lat su stl clk d orc t = SyncStage.syncRun lat su stl clk' d' orc' t :=
    run_congr _ _ (fun u hu => syncInp_congr h₁ h₂ h₃ hu) t (Nat.le_of_lt ht)
  unfold SyncStage.syncLen at ht
  rw [hrun, h₃.getD_eq_left (by omega)]

end Graphiti.AsyncFifo.Timed
