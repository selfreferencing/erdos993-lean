import Erdos993Lean.Analytic.Atlas.Data.U01
import Erdos993Lean.Analytic.Atlas.Data.U02
import Erdos993Lean.Analytic.Atlas.Data.U03
import Erdos993Lean.Analytic.Atlas.Data.U04
import Erdos993Lean.Analytic.Atlas.Data.U05
import Erdos993Lean.Analytic.Atlas.Data.U06
import Erdos993Lean.Analytic.Atlas.Data.U07
import Erdos993Lean.Analytic.Atlas.Data.U08
import Erdos993Lean.Analytic.Atlas.Data.U09
import Erdos993Lean.Analytic.Atlas.Data.U10
import Erdos993Lean.Analytic.Atlas.Data.U11
import Erdos993Lean.Analytic.Atlas.Data.U12
import Erdos993Lean.Analytic.Atlas.Data.U13
import Erdos993Lean.Analytic.Atlas.Data.U14
import Erdos993Lean.Analytic.Atlas.Data.U15
import Erdos993Lean.Analytic.Atlas.Data.U16
import Erdos993Lean.Analytic.Atlas.Data.U17
import Erdos993Lean.Analytic.Atlas.Data.U18
import Erdos993Lean.Analytic.Atlas.Data.U19
import Erdos993Lean.Analytic.Atlas.Data.U20
import Erdos993Lean.Analytic.Atlas.Data.U21
import Erdos993Lean.Analytic.Atlas.Data.U22
import Erdos993Lean.Analytic.Atlas.Data.U23
import Erdos993Lean.Analytic.Atlas.Data.U24
import Erdos993Lean.Analytic.Atlas.Data.U25
import Erdos993Lean.Analytic.Atlas.Data.U26
import Erdos993Lean.Analytic.Atlas.Data.U27
import Erdos993Lean.Analytic.Atlas.Data.U28
import Erdos993Lean.Analytic.Atlas.Data.U29
import Erdos993Lean.Analytic.Atlas.Data.U30

/-!
# Atlas data index: atlas_50_400_final (bands 1-30, `50 ≤ m ≤ 400`)

Band `i` (0-based) of the atlas: its boxes and its cover slabs (generated data, see the band modules).
-/

namespace Erdos993Lean.Analytic.Atlas.Data

open Erdos993Lean.Analytic.Atlas

/-- The boxes of band `i` (0-based) of atlas_50_400_final. -/
def upperBoxes : Nat → List Box
  | 0 => boxesU01
  | 1 => boxesU02
  | 2 => boxesU03
  | 3 => boxesU04
  | 4 => boxesU05
  | 5 => boxesU06
  | 6 => boxesU07
  | 7 => boxesU08
  | 8 => boxesU09
  | 9 => boxesU10
  | 10 => boxesU11
  | 11 => boxesU12
  | 12 => boxesU13
  | 13 => boxesU14
  | 14 => boxesU15
  | 15 => boxesU16
  | 16 => boxesU17
  | 17 => boxesU18
  | 18 => boxesU19
  | 19 => boxesU20
  | 20 => boxesU21
  | 21 => boxesU22
  | 22 => boxesU23
  | 23 => boxesU24
  | 24 => boxesU25
  | 25 => boxesU26
  | 26 => boxesU27
  | 27 => boxesU28
  | 28 => boxesU29
  | 29 => boxesU30
  | _ => []

/-- The cover slabs of band `i` (0-based) of atlas_50_400_final. -/
def upperSlabs : Nat → List Slab
  | 0 => slabsU01
  | 1 => slabsU02
  | 2 => slabsU03
  | 3 => slabsU04
  | 4 => slabsU05
  | 5 => slabsU06
  | 6 => slabsU07
  | 7 => slabsU08
  | 8 => slabsU09
  | 9 => slabsU10
  | 10 => slabsU11
  | 11 => slabsU12
  | 12 => slabsU13
  | 13 => slabsU14
  | 14 => slabsU15
  | 15 => slabsU16
  | 16 => slabsU17
  | 17 => slabsU18
  | 18 => slabsU19
  | 19 => slabsU20
  | 20 => slabsU21
  | 21 => slabsU22
  | 22 => slabsU23
  | 23 => slabsU24
  | 24 => slabsU25
  | 25 => slabsU26
  | 26 => slabsU27
  | 27 => slabsU28
  | 28 => slabsU29
  | 29 => slabsU30
  | _ => []

end Erdos993Lean.Analytic.Atlas.Data
