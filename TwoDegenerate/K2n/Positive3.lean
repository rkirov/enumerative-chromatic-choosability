/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Cert.K3N0
import TwoDegenerate.K2n.Cert.K3N1
import TwoDegenerate.K2n.Cert.K3N2
import TwoDegenerate.K2n.Cert.K3N3
import TwoDegenerate.K2n.Cert.K3N4
import TwoDegenerate.K2n.Cert.K3N5
import TwoDegenerate.K2n.Cert.K3N6
import TwoDegenerate.K2n.Cert.K3N7
import TwoDegenerate.K2n.Cert.K3N8
import TwoDegenerate.K2n.Cert.K3N9
import TwoDegenerate.K2n.Cert.K3N10
import TwoDegenerate.K2n.Cert.K3N11

/-!
# `K₂,ₙ` is ECC at 3 for every `n ≤ 11`

One generated certificate file per `n` (`TwoDegenerate/K2n/Cert/K3N*.lean`).
-/

namespace SimpleGraph.TwoDegenerate.K2n

theorem eccAt_3_of_le {n : ℕ} (hn : n ≤ 11) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 3 :=
  match n, hn with
  | 0, _ => Data.eccAt_3_0
  | 1, _ => Data.eccAt_3_1
  | 2, _ => Data.eccAt_3_2
  | 3, _ => Data.eccAt_3_3
  | 4, _ => Data.eccAt_3_4
  | 5, _ => Data.eccAt_3_5
  | 6, _ => Data.eccAt_3_6
  | 7, _ => Data.eccAt_3_7
  | 8, _ => Data.eccAt_3_8
  | 9, _ => Data.eccAt_3_9
  | 10, _ => Data.eccAt_3_10
  | 11, _ => Data.eccAt_3_11
  | _ + 12, h => absurd h (by omega)

end SimpleGraph.TwoDegenerate.K2n
