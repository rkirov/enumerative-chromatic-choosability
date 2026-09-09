/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.TwoCycles

/-!
The brute-force sweeps of `ListColoring/TwoCycles.lean`, moved here because they take about a
minute and a half of evaluation: not part of the default build, built by CI (`lake build Checks`).
-/

namespace ListColoring.Guards

-- every list really has two colours
#guard ((List.range 6).flatMap fun m => (List.range 6).flatMap fun n =>
  (List.range 6).map fun l =>
    ((List.range (m + 2 + l + n + 2 + 1)).map fun v =>
      (dumbL (m + 2) (n + 2) l v).card)).all fun cs => cs.all (· == 2)

-- and there is no colouring at all, for every shape in the sweep
#guard ((List.range 5).flatMap fun m => (List.range 5).flatMap fun n =>
  (List.range 5).map fun l => dumbCol (m + 2) (n + 2) l).all (· == 0)


end ListColoring.Guards
