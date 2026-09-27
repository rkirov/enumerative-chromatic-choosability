/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Cert.K4N0
import TwoDegenerate.K2n.Cert.K4N1
import TwoDegenerate.K2n.Cert.K4N2
import TwoDegenerate.K2n.Cert.K4N3
import TwoDegenerate.K2n.Cert.K4N4
import TwoDegenerate.K2n.Cert.K4N5
import TwoDegenerate.K2n.Cert.K4N6
import TwoDegenerate.K2n.Cert.K4N7
import TwoDegenerate.K2n.Cert.K4N8
import TwoDegenerate.K2n.Cert.K4N9
import TwoDegenerate.K2n.Cert.K4N10
import TwoDegenerate.K2n.Cert.K4N11
import TwoDegenerate.K2n.Cert.K4N12
import TwoDegenerate.K2n.Cert.K4N13
import TwoDegenerate.K2n.Cert.K4N14
import TwoDegenerate.K2n.Cert.K4N15
import TwoDegenerate.K2n.Cert.K4N16
import TwoDegenerate.K2n.Cert.K4N17
import TwoDegenerate.K2n.Cert.K4N18
import TwoDegenerate.K2n.Cert.K4N19
import TwoDegenerate.K2n.Cert.K4N20
import TwoDegenerate.K2n.Cert.K4N21
import TwoDegenerate.K2n.Cert.K4N22
import TwoDegenerate.K2n.Cert.K4N23
import TwoDegenerate.K2n.Cert.K4N24
import TwoDegenerate.K2n.Cert.K4N25

/-!
# `K₂,ₙ` is ECC at 4 for every `n ≤ 25`

One generated certificate file per `n` (`TwoDegenerate/K2n/Cert/K4N*.lean`).
-/

namespace SimpleGraph.TwoDegenerate.K2n

theorem eccAt_4_of_le {n : ℕ} (hn : n ≤ 25) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 4 :=
  match n, hn with
  | 0, _ => Data.eccAt_4_0
  | 1, _ => Data.eccAt_4_1
  | 2, _ => Data.eccAt_4_2
  | 3, _ => Data.eccAt_4_3
  | 4, _ => Data.eccAt_4_4
  | 5, _ => Data.eccAt_4_5
  | 6, _ => Data.eccAt_4_6
  | 7, _ => Data.eccAt_4_7
  | 8, _ => Data.eccAt_4_8
  | 9, _ => Data.eccAt_4_9
  | 10, _ => Data.eccAt_4_10
  | 11, _ => Data.eccAt_4_11
  | 12, _ => Data.eccAt_4_12
  | 13, _ => Data.eccAt_4_13
  | 14, _ => Data.eccAt_4_14
  | 15, _ => Data.eccAt_4_15
  | 16, _ => Data.eccAt_4_16
  | 17, _ => Data.eccAt_4_17
  | 18, _ => Data.eccAt_4_18
  | 19, _ => Data.eccAt_4_19
  | 20, _ => Data.eccAt_4_20
  | 21, _ => Data.eccAt_4_21
  | 22, _ => Data.eccAt_4_22
  | 23, _ => Data.eccAt_4_23
  | 24, _ => Data.eccAt_4_24
  | 25, _ => Data.eccAt_4_25
  | _ + 26, h => absurd h (by omega)

end SimpleGraph.TwoDegenerate.K2n
