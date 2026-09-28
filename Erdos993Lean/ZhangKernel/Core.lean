import Erdos993LeanZhangCompute.Checker.Core
import Erdos993Lean.ZhangKernel.Literals

/-!
# Kernel-checked finite part: the checker

T. Zhang's certificate layer for the finite part (*Exact Certificates for Unimodality of Forest
Independence Polynomials*, v1.1, Sections 2.7–2.10) is checked in `Erdos993Lean/ZhangCert/` by one
`native_decide` over the checker `ZhangCertX.checkRange`.  This module holds a second checker, written
for **evaluation by the Lean kernel** (`decide +kernel`); it imports only Lean's core, the literals of
`ZhangKernel/Literals.lean` and the computational core `Erdos993LeanZhangCompute/Checker/Core.lean`
(whose definitions it mirrors).  Its soundness is proved in `ZhangKernel/Generic.lean` and
`ZhangKernel/Direct.lean`: a passing kernel check implies `ZhangCertX.genericOK … = true` for a generic
certificate, and the bridge `ZhangCertX.genericOK_sound` gives `Cert.NoRecovery`.

**What is checked.**  For each triple `(n, a, k)` an item (`TItem`): either `direct h` (the direct
criterion `h` of `ZhangCertX.directOK`: `0` the path row `path(k)`, `1` the lower layer rule,
otherwise the upper layer rule) or `gen kind σ rows` (a generic certificate: kind, target scale `σ`,
weighted rows).  The items are data (`ZhangKernel/Data/`); soundness holds for arbitrary items.

**How** (measured in `ProofRuns/2026-09-28_analytic_large_n/LEAN/lanes/K/NOTES.md`):
* the kernel evaluates definitions by recursors (`Nat.rec`, `List.rec`) several times faster than
  structural recursion (compiled through `brecOn`), so every hot loop is written with a recursor
  (hence `noncomputable`: these definitions are only ever evaluated by the kernel);
* hot arithmetic uses the `Nat` primitives the kernel computes with GMP (`Nat.add`, `Nat.mul`,
  `Nat.ble`, `Nat.land`, `Nat.shiftLeft`, …) and `bif`, never type-class arithmetic;
* **packed rows**: for the layer `j` of a generic certificate, the coefficients `a^ℓ_{j,m}` of a row
  over `m = 0, …, a − j` are packed into one natural number, lane `m` (bits `384 m` to `384 m + 383`)
  holding the positive part and a second number holding the negative part (`packS`, with a flag that
  every part is at most `2^80`).  The weighted sum over the rows is then a few big-number operations
  per row (`accL`), and the residual of each `(j, m)` is read from two lanes (`laneMaxL`).  Each row's
  coefficient function is chosen once per layer (`rowFnO`), as a small closure;
* **direct criteria**: the residual of a direct criterion is `W_j · x_h(k − j, m)`, so the largest
  residual of a layer is `W_j · T_h(k − j, a − j)`, read from a packed table (`tabLane`, verified
  lane by lane in `ZhangKernel/LiteralChecks.lean`).
-/

namespace Erdos993Lean

namespace ZhangKernel

open ZhangCertX

/-! ### Constants -/

/-- The lane width of the packed vectors: `384` bits. -/
def LB : Nat := 384

/-- `2 ^ 384 − 1`, the mask of one lane. -/
def maskB : Nat :=
  39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306815

/-- `2 ^ 64 − 1`. -/
def mask64 : Nat := 18446744073709551615

/-- `2 ^ 80 − 1`: every packed coefficient part is at most `partB + 1`. -/
def partB : Nat := 1208925819614629174706175

/-- `2 ^ 250`: the bound on the total weight of a generic certificate. -/
def wBound : Nat :=
  1809251394333065553493296640760748560207343510400633813116524750123642650624

/-- `2 ^ 240`: the bound on the target scale of a generic certificate. -/
def sigBound : Nat :=
  1766847064778384329583297500742918515827483896875618958121606201292619776

/-- `2 ^ 62`: the offset of the table lanes. -/
def tabOff : Nat := 4611686018427387904

/-! ### Binomial coefficients and integers -/

/-- `C(m, r)`: a lane of the packed row `bRow m` for `m, r < 64`, the formula `binomF` otherwise
(the mirror of `ZhangCertX.binomN`). -/
def chooseK (m r : Nat) : Nat :=
  bif Nat.ble 64 m || Nat.ble 64 r then binomF m r
  else Nat.land (Nat.shiftRight (bRow m) (Nat.mul 64 r)) mask64

/-- The paper's binomial over the integers (the mirror of `ZhangCertX.binomZ`). -/
def binomZK (b r : Int) : Int :=
  match b, r with
  | .ofNat b, .ofNat r => Int.ofNat (chooseK b r)
  | _, _ => Int.ofNat 0

/-- `x ≤ y` on the integers. -/
def leK : Int → Int → Bool
  | .ofNat x, .ofNat y => Nat.ble x y
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc x, .negSucc y => Nat.ble y x

/-- `max x y` on the integers. -/
def maxK (x y : Int) : Int := bif leK x y then y else x

/-- `x = y` on the integers. -/
def eqK (x y : Int) : Bool := leK x y && leK y x

/-- The sign test of a bound (the mirror of `ZhangCertX.signOK`). -/
def signK (kind : Kind) (b : Int) : Bool :=
  match kind with
  | .pos => !(leK (Int.ofNat 0) b)
  | .neg => leK b (Int.ofNat 0)
  | .cond => leK b (Int.ofNat 0)

/-! ### Mirrors of the rows of `ZhangCertX` -/

/-- `B_{m,j}(k)` (the mirror of `ZhangCertX.BZ`). -/
def BZK (m j k : Nat) : Int :=
  bif Nat.ble j k then
    Int.subNatNat (chooseK m (Nat.sub k j))
      (bif Nat.beq j k then 0 else chooseK m (Nat.sub (Nat.sub k j) 1))
  else Int.ofNat 0

/-- The target constant (the mirror of `ZhangCertX.tgt0Z`). -/
def tgt0K (kind : Kind) (a k : Nat) : Int :=
  match kind with
  | .pos => Int.neg (BZK a 0 k)
  | .neg => BZK a 0 (Nat.add k 1)
  | .cond => BZK a 0 (Nat.add k 1)

/-- `posZ (((r : Int) − 1) m + a − r + 1 − r h)` as a natural number. -/
def privPos (a r h m : Nat) : Nat :=
  bif Nat.beq r 0 then Nat.sub (Nat.add a 1) m
  else Nat.sub (Nat.add (Nat.mul (Nat.sub r 1) m) (Nat.add a 1)) (Nat.add r (Nat.mul r h))

/-- The factor of `hall(r, l)` (the mirror of `ZhangCertX.hallCZ`). -/
def hallCK (n a r l : Nat) : Int := Int.subNatNat (vP n a) (Nat.add r (Nat.sub l (δP n a)))

/-- `b_{r,h}(m)` (the mirror of `ZhangCertX.bStepZ`). -/
def bStepK (a r h m : Nat) : Nat :=
  bif Nat.ble h m then r
  else bif Nat.ble (Nat.mul r h) (Nat.add a (Nat.mul (Nat.sub r 1) m)) then 1 else 0

/-- `s_r` (the mirror of `ZhangCertX.sExtZ`). -/
def sExtK (n a r : Nat) : Nat := Nat.sub (Nat.add (vP n a) 1) (Nat.add r (EP n a))

/-- `U_{r,h}(m)` (the mirror of `ZhangCertX.UZ`). -/
def UK (a r h m : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.div (Nat.sub a m) (Nat.sub (Nat.add (Nat.sub a m) 1) r))
      (Nat.sub (Nat.add m (Nat.sub (Nat.add (Nat.sub a m) 1) r)) h))
    (bif Nat.ble r (Nat.div (Nat.sub a m) (Nat.sub (Nat.add (Nat.sub a m) 1) r)) then 0
     else Nat.add
       (Nat.sub (Nat.add m (Nat.mod (Nat.sub a m) (Nat.sub (Nat.add (Nat.sub a m) 1) r))) h)
       (Nat.mul (Nat.sub (Nat.sub r (Nat.div (Nat.sub a m) (Nat.sub (Nat.add (Nat.sub a m) 1) r))) 1)
         (Nat.sub m h)))

/-- `V_{r,h}(m)` (the mirror of `ZhangCertX.VtZ`). -/
def VtK (a r h m : Nat) : Nat :=
  bif Nat.ble h m then r
  else bif Nat.ble h (Nat.add m (Nat.sub (Nat.add (Nat.sub a m) 1) r)) then
    Nat.min r (Nat.div (Nat.sub a m) (Nat.sub h m))
  else 0

/-- `β_r` (the mirror of `ZhangCertX.βZ`). -/
def βK (n a r : Nat) : Int :=
  Int.add (binomZK (Int.subNatNat (vP n a) 2) (Int.subNatNat r 1))
    (Int.neg (Int.mul (Int.subNatNat a 2) (binomZK (Int.subNatNat (vP n a) 2) (Int.subNatNat r 2))))

/-- `C_r^0` (the mirror of `ZhangCertX.C0Z`). -/
def C0K (n a r : Nat) : Int :=
  Int.add (Int.mul (Int.ofNat a) (binomZK (Int.subNatNat (vP n a) 2) (Int.ofNat r)))
    (Int.mul (Int.ofNat (Nat.add (δP n a) 1)) (binomZK (Int.subNatNat (vP n a) 2) (Int.subNatNat r 1)))

/-- `G_r` (the mirror of `ZhangCertX.GrZ`). -/
def GrK (n a r : Nat) : Int :=
  Int.add (binomZK (Int.subNatNat (vP n a) 1) (Int.subNatNat r 1))
    (Int.neg (binomZK (Int.subNatNat (vP n a) (Nat.add (D0P n a) 1)) (Int.subNatNat r 1)))

/-- The coefficient `a^ℓ_{j,m}` (the mirror of `ZhangCertX.coefZ`). -/
def coefK (n a : Nat) : CLabel → Nat → Nat → Int
  | .count r, j, _ => bif Nat.beq j r then Int.ofNat 1 else Int.ofNat 0
  | .path r, j, m => bif Nat.ble j r then Int.negOfNat (chooseK m (Nat.sub r j)) else Int.ofNat 0
  | .priv r h, j, m =>
      Int.add (bif Nat.beq j r then Int.ofNat (privPos a r h m) else Int.ofNat 0)
        (bif Nat.beq j (Nat.sub r 1) then
          Int.neg (Int.mul (Int.subNatNat (Nat.add (vP n a) 1) r) (Int.ofNat (Nat.sub m h)))
         else Int.ofNat 0)
  | .hall r l, j, m =>
      bif Nat.beq j (Nat.add r 1) then Int.ofNat (Nat.mul (Nat.add r 1) (chooseK m l))
      else bif Nat.beq j r then Int.neg (Int.mul (hallCK n a r l) (Int.ofNat (chooseK m l)))
      else Int.ofNat 0
  | .tail r h, j, m =>
      Int.add (bif Nat.beq j r then Int.ofNat (bStepK a r h m) else Int.ofNat 0)
        (bif Nat.beq j (Nat.sub r 1) && Nat.ble h m then
          Int.neg (Int.subNatNat (Nat.add (vP n a) 1) r) else Int.ofNat 0)
  | .releaseUpper r h, j, m =>
      Int.add (bif Nat.beq j (Nat.sub r 1) then Int.ofNat (Nat.mul (sExtK n a r) (Nat.sub m h))
        else Int.ofNat 0)
        (bif Nat.beq j r then Int.negOfNat (UK a r h m) else Int.ofNat 0)
  | .tailUpper r h, j, m =>
      Int.add (bif Nat.beq j (Nat.sub r 1) && Nat.ble h m then Int.ofNat (sExtK n a r)
        else Int.ofNat 0)
        (bif Nat.beq j r then Int.negOfNat (VtK a r h m) else Int.ofNat 0)
  | .mean r, j, m =>
      Int.add (bif Nat.beq j r then Int.negOfNat m else Int.ofNat 0)
        (bif Nat.beq j 2 then Int.neg (βK n a r) else Int.ofNat 0)
  | .union r, j, m =>
      Int.mul (Int.subNatNat a m)
        (Int.add (bif Nat.beq j r then Int.ofNat 1 else Int.ofNat 0)
          (bif Nat.beq j 1 then Int.neg (binomZK (Int.subNatNat (vP n a) 1) (Int.subNatNat r 1))
           else Int.ofNat 0))
  | .edgeLower r, j, _ =>
      Int.add (bif Nat.beq j r then Int.negOfNat 1 else Int.ofNat 0)
        (bif Nat.beq j 2 then binomZK (Int.subNatNat (vP n a) 2) (Int.subNatNat r 2)
         else Int.ofNat 0)
  | .edgeUpper r, j, _ =>
      Int.add (bif Nat.beq j r then Int.ofNat (D0P n a) else Int.ofNat 0)
        (bif Nat.beq j 2 then Int.neg (GrK n a r) else Int.ofNat 0)
  | .assumption k, j, m => BZK m j k

/-- The right side `b^ℓ` (the mirror of `ZhangCertX.rhsZ`). -/
def rhsK (n a : Nat) : CLabel → Int
  | .count r => binomZK (Int.ofNat (vP n a)) (Int.ofNat r)
  | .path r => Int.add (binomZK (Int.ofNat a) (Int.ofNat r))
      (Int.neg (binomZK (Int.subNatNat (Nat.add n 1) r) (Int.ofNat r)))
  | .priv _ _ => Int.ofNat 0
  | .hall r l => bif Nat.beq r 0 then Int.mul (hallCK n a r l) (binomZK (Int.ofNat a) (Int.ofNat l))
      else Int.ofNat 0
  | .tail _ _ => Int.ofNat 0
  | .releaseUpper _ _ => Int.ofNat 0
  | .tailUpper _ _ => Int.ofNat 0
  | .mean r => Int.add (Int.neg (C0K n a r))
      (Int.neg (Int.mul (βK n a r) (binomZK (Int.ofNat (vP n a)) (Int.ofNat 2))))
  | .union _ => Int.ofNat 0
  | .edgeLower r => Int.add (Int.neg (binomZK (Int.ofNat (vP n a)) (Int.ofNat r)))
      (Int.mul (binomZK (Int.subNatNat (vP n a) 2) (Int.subNatNat r 2))
        (binomZK (Int.ofNat (vP n a)) (Int.ofNat 2)))
  | .edgeUpper r => Int.add (Int.mul (Int.ofNat (D0P n a)) (binomZK (Int.ofNat (vP n a)) (Int.ofNat r)))
      (Int.neg (Int.mul (GrK n a r) (binomZK (Int.ofNat (vP n a)) (Int.ofNat 2))))
  | .assumption k => Int.neg (BZK a 0 k)

/-! ### The coefficient function of a row on a layer -/

/-- `count(r)` on the layer `j`. -/
def rfCount (j r : Nat) : Option (Nat → Int) :=
  bif Nat.beq j r then some (fun _ => Int.ofNat 1) else none

/-- `path(r)` on the layer `j`. -/
def rfPath (j r : Nat) : Option (Nat → Int) :=
  bif Nat.ble j r then some (fun m => Int.negOfNat (chooseK m (Nat.sub r j))) else none

/-- `private(r, h)` on the layer `j`. -/
def rfPriv (n a r h j : Nat) : Option (Nat → Int) :=
  bif Nat.beq j r then some (fun m => Int.ofNat (privPos a r h m))
  else bif Nat.beq j (Nat.sub r 1) then
    (bif Nat.ble r (Nat.add (vP n a) 1) then
      some (fun m => Int.negOfNat (Nat.mul (Nat.sub (Nat.add (vP n a) 1) r) (Nat.sub m h)))
     else some (fun m => Int.ofNat (Nat.mul (Nat.sub r (Nat.add (vP n a) 1)) (Nat.sub m h))))
  else none

/-- `hall(r, l)` on the layer `j`. -/
def rfHall (n a r l j : Nat) : Option (Nat → Int) :=
  bif Nat.beq j (Nat.add r 1) then some (fun m => Int.ofNat (Nat.mul (Nat.add r 1) (chooseK m l)))
  else bif Nat.beq j r then
    (bif Nat.ble (Nat.add r (Nat.sub l (δP n a))) (vP n a) then
      some (fun m => Int.negOfNat
        (Nat.mul (Nat.sub (vP n a) (Nat.add r (Nat.sub l (δP n a)))) (chooseK m l)))
     else some (fun m => Int.ofNat
        (Nat.mul (Nat.sub (Nat.add r (Nat.sub l (δP n a))) (vP n a)) (chooseK m l))))
  else none

/-- `tail(r, h)` on the layer `j`. -/
def rfTail (n a r h j : Nat) : Option (Nat → Int) :=
  bif Nat.beq j r then some (fun m => Int.ofNat (bStepK a r h m))
  else bif Nat.beq j (Nat.sub r 1) then
    (bif Nat.ble r (Nat.add (vP n a) 1) then
      some (fun m => bif Nat.ble h m then Int.negOfNat (Nat.sub (Nat.add (vP n a) 1) r)
        else Int.ofNat 0)
     else some (fun m => bif Nat.ble h m then Int.ofNat (Nat.sub r (Nat.add (vP n a) 1))
        else Int.ofNat 0))
  else none

/-- `assumption(k)` on the layer `j`. -/
def rfAssumption (j k : Nat) : Option (Nat → Int) :=
  bif Nat.ble j k then some (fun m => BZK m j k) else none

/-- Any other row on the layer `j` (through `coefK`). -/
def rfGeneric (n a : Nat) (ℓ : CLabel) (j : Nat) : Option (Nat → Int) :=
  bif touches ℓ j then some (fun m => coefK n a ℓ j m) else none

/-- **The coefficient function of the row `ℓ` on the layer `j ≥ 1`**: `none` if the row vanishes
on the layer, else a function equal to `m ↦ coefK n a ℓ j m`. -/
def rowFnO (n a : Nat) (ℓ : CLabel) (j : Nat) : Option (Nat → Int) :=
  match ℓ with
  | .count r => rfCount j r
  | .path r => rfPath j r
  | .priv r h => rfPriv n a r h j
  | .hall r l => rfHall n a r l j
  | .tail r h => rfTail n a r h j
  | .assumption k => rfAssumption j k
  | ℓ => rfGeneric n a ℓ j

/-! ### Packed vectors -/

/-- **Packing.**  Adds the positive parts of `f m, …, f (m + c − 1)` to `P` and their negative
parts to `N`, lane `i` at bit `sh + 384 i`, and records whether every part is at most `2^80`. -/
noncomputable def packS (f : Nat → Int) (c : Nat) :
    Nat → Nat → Nat → Nat → Bool → Nat × Nat × Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool → Nat × Nat × Bool)
    (fun _ _ P N ok => (P, N, ok))
    (fun _ ih m sh P N ok =>
      match f m with
      | .ofNat x =>
        ih (Nat.add m 1) (Nat.add sh LB) (Nat.add P (Nat.shiftLeft x sh)) N (and ok (Nat.ble x partB))
      | .negSucc x =>
        ih (Nat.add m 1) (Nat.add sh LB) P (Nat.add N (Nat.shiftLeft (Nat.add x 1) sh))
          (and ok (Nat.ble x partB)))
    c

/-- The weighted packed rows of a layer: `P + Σ w · (positive parts)`, `N + Σ w · (negative
parts)` over the rows that do not vanish on the layer `j` (lanes `m < L`). -/
noncomputable def accL (n a j L : Nat) (rows : List (CLabel × Nat)) :
    Nat → Nat → Bool → Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool → Nat × Nat × Bool)
    (fun P N ok => (P, N, ok))
    (fun p _ ih P N ok =>
      match rowFnO n a p.1 j with
      | none => ih P N ok
      | some f =>
        ih (Nat.add P (Nat.mul p.2 (packS f L 0 0 0 0 true).1))
          (Nat.add N (Nat.mul p.2 (packS f L 0 0 0 0 true).2.1))
          (and ok (packS f L 0 0 0 0 true).2.2))
    rows

/-- The packed Pascal column `C(m, r)`, `m < L`. -/
noncomputable def colS (r L : Nat) : Nat × Nat × Bool :=
  packS (fun m => Int.ofNat (chooseK m r)) L 0 0 0 0 true

/-- The positive part of the target on the layer `j`: `C(m, k − j − 1)` (`pos`) or
`C(m, k + 1 − j)` (otherwise). -/
noncomputable def tgtPS (kind : Kind) (k j L : Nat) : Nat × Nat × Bool :=
  match kind with
  | .pos => bif Nat.ble (Nat.add j 1) k then colS (Nat.sub (Nat.sub k j) 1) L else (0, 0, true)
  | .neg => bif Nat.ble j (Nat.add k 1) then colS (Nat.sub (Nat.add k 1) j) L else (0, 0, true)
  | .cond => bif Nat.ble j (Nat.add k 1) then colS (Nat.sub (Nat.add k 1) j) L else (0, 0, true)

/-- The negative part of the target on the layer `j`: `C(m, k − j)`. -/
noncomputable def tgtQS (k j L : Nat) : Nat × Nat × Bool :=
  bif Nat.ble j k then colS (Nat.sub k j) L else (0, 0, true)

/-- The best lane: over the lanes of `X` and `Y` (starting from the pair `(xb, yb)`), the pair
`(x, y)` of lanes with the largest `x − y`. -/
noncomputable def laneMaxL (c : Nat) : Nat → Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat × Nat)
    (fun _ _ xb yb => (xb, yb))
    (fun _ ih X Y xb yb =>
      ih (Nat.shiftRight X LB) (Nat.shiftRight Y LB)
        (bif Nat.ble (Nat.add xb (Nat.land Y maskB)) (Nat.add (Nat.land X maskB) yb)
          then Nat.land X maskB else xb)
        (bif Nat.ble (Nat.add xb (Nat.land Y maskB)) (Nat.add (Nat.land X maskB) yb)
          then Nat.land Y maskB else yb))
    c

/-- **The layer `j` of a generic certificate**: `(x, y, ok)` with `x − y` the largest
`σ · tgt_{j,m} − Σ w a_{j,m}` over `0 ≤ m ≤ a − j` (the residual divided by `W_j`), `ok` the
bound flags. -/
noncomputable def layerD (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat))
    (j : Nat) : Nat × Nat × Bool :=
  let L := Nat.sub (Nat.add a 1) j
  let acc := accL n a j L rows 0 0 true
  let tp := tgtPS kind k j L
  let tq := tgtQS k j L
  let X := Nat.add (Nat.mul σ tp.1) acc.2.1
  let Y := Nat.add (Nat.mul σ tq.1) acc.1
  let d := laneMaxL (Nat.sub L 1) (Nat.shiftRight X LB) (Nat.shiftRight Y LB) (Nat.land X maskB)
    (Nat.land Y maskB)
  (d.1, d.2, and acc.2.2 (and tp.2.2 tq.2.2))

/-- `S + Σ max(0, W_j (x_j − y_j))` over the layers `j = j₀, …, j₀ + c − 1`, and the flags. -/
noncomputable def sumLayers (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat))
    (c : Nat) : Nat → Int → Bool → Int × Bool :=
  Nat.rec (motive := fun _ => Nat → Int → Bool → Int × Bool)
    (fun _ S ok => (S, ok))
    (fun _ ih j S ok =>
      ih (Nat.add j 1)
        (Int.add S (maxK (Int.ofNat 0) (Int.mul (Int.ofNat (chooseK (vP n a) j))
          (Int.subNatNat (layerD n a k kind σ rows j).1 (layerD n a k kind σ rows j).2.1))))
        (and ok (layerD n a k kind σ rows j).2.2))
    c

/-- `acc + Σ w · b^ℓ` over the rows. -/
noncomputable def rhsSumK (n a : Nat) (rows : List (CLabel × Nat)) : Int → Int :=
  List.rec (motive := fun _ => Int → Int) (fun acc => acc)
    (fun p _ ih acc => ih (Int.add acc (Int.mul (Int.ofNat p.2) (rhsK n a p.1)))) rows

/-- `acc + Σ w` over the rows. -/
noncomputable def sumW (rows : List (CLabel × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun p _ ih acc => ih (Nat.add acc p.2)) rows

/-- **The generic certificate check, kernel form.**  Passing implies
`ZhangCertX.genericOK n a k kind σ rows = true` (`ZhangKernel.genericOK_of_genericOKV`). -/
noncomputable def genericOKV (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat)) :
    Bool :=
  Nat.ble 1 (vP n a) && Nat.ble (vP n a) a && Nat.ble a 63 && Nat.ble 1 σ && Nat.ble σ sigBound &&
    rows.all (fun p => rowOKB n a k kind p.1) && Nat.ble (sumW rows 0) wBound &&
    (layerD n a k kind σ rows 1).2.2 &&
    (sumLayers n a k kind σ rows (Nat.sub (vP n a) 1) 2 (Int.ofNat 0) true).2 &&
    signK kind (Int.add (Int.add (Int.add (Int.mul (Int.ofNat σ) (tgt0K kind a k))
      (rhsSumK n a rows (Int.ofNat 0)))
      (Int.mul (Int.ofNat (chooseK (vP n a) 1))
        (Int.subNatNat (layerD n a k kind σ rows 1).1 (layerD n a k kind σ rows 1).2.1)))
      (sumLayers n a k kind σ rows (Nat.sub (vP n a) 1) 2 (Int.ofNat 0) true).1)

/-! ### The direct criteria -/

/-- The lane `M` of the packed table row `tabRow h r`, minus the offset: `T_h(r, M)`. -/
def tabLane (h r M : Nat) : Int :=
  Int.subNatNat (Nat.land (Nat.shiftRight (tabRow h r) (Nat.mul 64 M)) mask64) tabOff

/-- The value `x_h(r, m)` of the tables (see `ZhangKernel/Literals.lean`). -/
def xRef (h r m : Nat) : Int :=
  bif Nat.beq h 0 then Int.add (Int.neg (BZK m 0 r)) (Int.ofNat (chooseK m r))
  else bif Nat.beq h 1 then Int.neg (BZK m 0 r) else BZK m 0 r

/-- `acc + Σ f j` over `j = j₀, …, j₀ + c − 1`. -/
noncomputable def sumLoopR (f : Nat → Int) (c : Nat) : Nat → Int → Int :=
  Nat.rec (motive := fun _ => Nat → Int → Int) (fun _ acc => acc)
    (fun _ ih j acc => ih (Nat.add j 1) (Int.add acc (f j))) c

/-- **The direct criterion `h`, kernel form**: `0` the path row `path(k)` with weight `1`, `1` the
lower layer rule, otherwise the upper layer rule, each with target scale `1`.  The largest residual
of the layer `j` is `W_j · T_h(r − j, a − j)` with `r = k` (`h ≤ 1`) or `r = k + 1`, from the tables. -/
noncomputable def directV (n a k h : Nat) : Bool :=
  Nat.ble 1 (vP n a) && Nat.ble (vP n a) a && Nat.ble a 63 && Nat.ble 1 k &&
    Nat.ble (bif Nat.ble 2 h then Nat.add k 1 else k) 63 &&
    (bif Nat.beq h 0 then Nat.ble 2 k && Nat.ble k a else true) &&
    signK (bif Nat.ble 2 h then .neg else .pos)
      (Int.add (Int.add (Int.add (tgt0K (bif Nat.ble 2 h then .neg else .pos) a k)
        (bif Nat.beq h 0 then rhsK n a (.path k) else Int.ofNat 0))
        (Int.mul (Int.ofNat (chooseK (vP n a) 1))
          (tabLane h (Nat.sub (bif Nat.ble 2 h then Nat.add k 1 else k) 1) (Nat.sub a 1))))
        (sumLoopR (fun j =>
          bif Nat.ble j (bif Nat.ble 2 h then Nat.add k 1 else k) then
            maxK (Int.ofNat 0) (Int.mul (Int.ofNat (chooseK (vP n a) j))
              (tabLane h (Nat.sub (bif Nat.ble 2 h then Nat.add k 1 else k) j) (Nat.sub a j)))
          else Int.ofNat 0) (Nat.sub (vP n a) 1) 2 (Int.ofNat 0)))

/-! ### Items and slices -/

/-- The check item of a triple: a direct criterion or a generic certificate. -/
inductive TItem where
  | direct (h : Nat)
  | gen (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat))

/-- The check of one item. -/
noncomputable def itemOKV (n a k : Nat) : TItem → Bool
  | .direct h => directV n a k h
  | .gen kind σ rows => genericOKV n a k kind σ rows

/-- The items of `k₀, …, k₀ + c − 1`. -/
noncomputable def checkKsV (n a : Nat) : Nat → Nat → List TItem → Bool
  | _, 0, _ => true
  | _, _ + 1, [] => false
  | k, c + 1, it :: rest => itemOKV n a k it && checkKsV n a (Nat.add k 1) c rest

/-- **The check of `(n, a)`**: the items of every `1 ≤ k < ⌊(2a + 1)/3⌋`. -/
noncomputable def checkAV (n a : Nat) (items : List TItem) : Bool :=
  checkKsV n a 1 (Nat.sub (Nat.div (Nat.add (Nat.mul 2 a) 1) 3) 1) items

/-- **The check of the order `n`**: the item lists of `a, a + 1, …, n − 1`. -/
noncomputable def checkOrderV (n : Nat) : Nat → List (List TItem) → Bool
  | a, [] => Nat.beq a n
  | a, items :: rest => checkAV n a items && checkOrderV n (Nat.add a 1) rest

end ZhangKernel

end Erdos993Lean
