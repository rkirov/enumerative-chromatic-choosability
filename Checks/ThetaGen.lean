/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.ThetaGen

/-! The witness sweeps of `ListColoring/ThetaGen.lean` (about fifteen seconds). -/

namespace ListColoring

-- **The sweep.** Every sorted valid shape with four or five arms and total length at most `12`.
#guard (gShapes 4 12).all gWitnessCheck#guard (gShapes 5 12).all gWitnessCheck

-- A few larger ones, past the range of the sweep.
#guard gWitnessCheck [2, 2, 2, 6]#guard gWitnessCheck [4, 4, 4, 4]
#guard gWitnessCheck [2, 2, 5, 5]
#guard gWitnessCheck [1, 2, 2, 3, 3]

end ListColoring
