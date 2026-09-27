/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Cert.K5N0
import TwoDegenerate.K2n.Cert.K5N1
import TwoDegenerate.K2n.Cert.K5N2
import TwoDegenerate.K2n.Cert.K5N3
import TwoDegenerate.K2n.Cert.K5N4
import TwoDegenerate.K2n.Cert.K5N5
import TwoDegenerate.K2n.Cert.K5N6
import TwoDegenerate.K2n.Cert.K5N7
import TwoDegenerate.K2n.Cert.K5N8
import TwoDegenerate.K2n.Cert.K5N9
import TwoDegenerate.K2n.Cert.K5N10
import TwoDegenerate.K2n.Cert.K5N11
import TwoDegenerate.K2n.Cert.K5N12
import TwoDegenerate.K2n.Cert.K5N13
import TwoDegenerate.K2n.Cert.K5N14
import TwoDegenerate.K2n.Cert.K5N15
import TwoDegenerate.K2n.Cert.K5N16
import TwoDegenerate.K2n.Cert.K5N17
import TwoDegenerate.K2n.Cert.K5N18
import TwoDegenerate.K2n.Cert.K5N19
import TwoDegenerate.K2n.Cert.K5N20
import TwoDegenerate.K2n.Cert.K5N21
import TwoDegenerate.K2n.Cert.K5N22
import TwoDegenerate.K2n.Cert.K5N23
import TwoDegenerate.K2n.Cert.K5N24
import TwoDegenerate.K2n.Cert.K5N25
import TwoDegenerate.K2n.Cert.K5N26
import TwoDegenerate.K2n.Cert.K5N27
import TwoDegenerate.K2n.Cert.K5N28
import TwoDegenerate.K2n.Cert.K5N29
import TwoDegenerate.K2n.Cert.K5N30
import TwoDegenerate.K2n.Cert.K5N31
import TwoDegenerate.K2n.Cert.K5N32
import TwoDegenerate.K2n.Cert.K5N33
import TwoDegenerate.K2n.Cert.K5N34
import TwoDegenerate.K2n.Cert.K5N35
import TwoDegenerate.K2n.Cert.K5N36
import TwoDegenerate.K2n.Cert.K5N37
import TwoDegenerate.K2n.Cert.K5N38
import TwoDegenerate.K2n.Cert.K5N39
import TwoDegenerate.K2n.Cert.K5N40
import TwoDegenerate.K2n.Cert.K5N41
import TwoDegenerate.K2n.Cert.K5N42
import TwoDegenerate.K2n.Cert.K5N43

/-!
# `K₂,ₙ` is ECC at 5 for every `n ≤ 43`

One generated certificate file per `n` (`TwoDegenerate/K2n/Cert/K5N*.lean`).
-/

namespace SimpleGraph.TwoDegenerate.K2n

theorem eccAt_5_of_le {n : ℕ} (hn : n ≤ 43) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 5 :=
  match n, hn with
  | 0, _ => Data.eccAt_5_0
  | 1, _ => Data.eccAt_5_1
  | 2, _ => Data.eccAt_5_2
  | 3, _ => Data.eccAt_5_3
  | 4, _ => Data.eccAt_5_4
  | 5, _ => Data.eccAt_5_5
  | 6, _ => Data.eccAt_5_6
  | 7, _ => Data.eccAt_5_7
  | 8, _ => Data.eccAt_5_8
  | 9, _ => Data.eccAt_5_9
  | 10, _ => Data.eccAt_5_10
  | 11, _ => Data.eccAt_5_11
  | 12, _ => Data.eccAt_5_12
  | 13, _ => Data.eccAt_5_13
  | 14, _ => Data.eccAt_5_14
  | 15, _ => Data.eccAt_5_15
  | 16, _ => Data.eccAt_5_16
  | 17, _ => Data.eccAt_5_17
  | 18, _ => Data.eccAt_5_18
  | 19, _ => Data.eccAt_5_19
  | 20, _ => Data.eccAt_5_20
  | 21, _ => Data.eccAt_5_21
  | 22, _ => Data.eccAt_5_22
  | 23, _ => Data.eccAt_5_23
  | 24, _ => Data.eccAt_5_24
  | 25, _ => Data.eccAt_5_25
  | 26, _ => Data.eccAt_5_26
  | 27, _ => Data.eccAt_5_27
  | 28, _ => Data.eccAt_5_28
  | 29, _ => Data.eccAt_5_29
  | 30, _ => Data.eccAt_5_30
  | 31, _ => Data.eccAt_5_31
  | 32, _ => Data.eccAt_5_32
  | 33, _ => Data.eccAt_5_33
  | 34, _ => Data.eccAt_5_34
  | 35, _ => Data.eccAt_5_35
  | 36, _ => Data.eccAt_5_36
  | 37, _ => Data.eccAt_5_37
  | 38, _ => Data.eccAt_5_38
  | 39, _ => Data.eccAt_5_39
  | 40, _ => Data.eccAt_5_40
  | 41, _ => Data.eccAt_5_41
  | 42, _ => Data.eccAt_5_42
  | 43, _ => Data.eccAt_5_43
  | _ + 44, h => absurd h (by omega)

end SimpleGraph.TwoDegenerate.K2n
