/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.RubinHard

/-! The `colConst` cross-checks of `ListColoring/RubinHard.lean` (about twenty seconds). -/

namespace ListColoring

#guard (thetaGen 2 2 2).colConst 2 = (theta 1).colConst 2#guard (thetaGen 2 2 2).colConst 3 = (theta 1).colConst 3
#guard (thetaGen 2 2 2).colConst 4 = (theta 1).colConst 4
#guard (thetaGen 2 2 4).colConst 2 = (theta 2).colConst 2
#guard (thetaGen 2 2 4).colConst 3 = (theta 2).colConst 3
#guard (thetaGen 2 2 4).colConst 4 = (theta 2).colConst 4
#guard (thetaGen 2 2 6).colConst 3 = (theta 3).colConst 3

end ListColoring
