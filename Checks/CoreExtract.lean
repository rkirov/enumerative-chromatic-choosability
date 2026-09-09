/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.CoreExtract

/-! The `colConst` cross-checks of `ListColoring/CoreExtract.lean` (about ten seconds). -/

namespace ListColoring

#guard (thetaOf 4).colConst 3 = (thetaGen 2 2 4).colConst 3
#guard (thetaOf 6).colConst 3 = (thetaGen 2 2 6).colConst 3

end ListColoring
