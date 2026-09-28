import Erdos993Lean.Analytic.Atlas.Data.L01
import Erdos993Lean.Analytic.Atlas.Data.L02
import Erdos993Lean.Analytic.Atlas.Data.L03
import Erdos993Lean.Analytic.Atlas.Data.L04
import Erdos993Lean.Analytic.Atlas.Data.L05
import Erdos993Lean.Analytic.Atlas.Data.L06
import Erdos993Lean.Analytic.Atlas.Data.L07
import Erdos993Lean.Analytic.Atlas.Data.L08
import Erdos993Lean.Analytic.Atlas.Data.L09
import Erdos993Lean.Analytic.Atlas.Data.L10
import Erdos993Lean.Analytic.Atlas.Data.L11
import Erdos993Lean.Analytic.Atlas.Data.L12
import Erdos993Lean.Analytic.Atlas.Data.L13
import Erdos993Lean.Analytic.Atlas.Data.L14
import Erdos993Lean.Analytic.Atlas.Data.L15
import Erdos993Lean.Analytic.Atlas.Data.L16
import Erdos993Lean.Analytic.Atlas.Data.L17
import Erdos993Lean.Analytic.Atlas.Data.L18
import Erdos993Lean.Analytic.Atlas.Data.L19
import Erdos993Lean.Analytic.Atlas.Data.L20
import Erdos993Lean.Analytic.Atlas.Data.L21
import Erdos993Lean.Analytic.Atlas.Data.L22
import Erdos993Lean.Analytic.Atlas.Data.L23
import Erdos993Lean.Analytic.Atlas.Data.L24
import Erdos993Lean.Analytic.Atlas.Data.L25
import Erdos993Lean.Analytic.Atlas.Data.L26
import Erdos993Lean.Analytic.Atlas.Data.L27
import Erdos993Lean.Analytic.Atlas.Data.L28
import Erdos993Lean.Analytic.Atlas.Data.L29
import Erdos993Lean.Analytic.Atlas.Data.L30

/-!
# Atlas data index: atlas_50 (bands 1-30, `m ≤ 50`)

Band `i` (0-based) of the atlas: its boxes and its cover slabs (generated data, see the band modules).
-/

namespace Erdos993Lean.Analytic.Atlas.Data

open Erdos993Lean.Analytic.Atlas

/-- The boxes of band `i` (0-based) of atlas_50. -/
def lowerBoxes : Nat → List Box
  | 0 => boxesL01
  | 1 => boxesL02
  | 2 => boxesL03
  | 3 => boxesL04
  | 4 => boxesL05
  | 5 => boxesL06
  | 6 => boxesL07
  | 7 => boxesL08
  | 8 => boxesL09
  | 9 => boxesL10
  | 10 => boxesL11
  | 11 => boxesL12
  | 12 => boxesL13
  | 13 => boxesL14
  | 14 => boxesL15
  | 15 => boxesL16
  | 16 => boxesL17
  | 17 => boxesL18
  | 18 => boxesL19
  | 19 => boxesL20
  | 20 => boxesL21
  | 21 => boxesL22
  | 22 => boxesL23
  | 23 => boxesL24
  | 24 => boxesL25
  | 25 => boxesL26
  | 26 => boxesL27
  | 27 => boxesL28
  | 28 => boxesL29
  | 29 => boxesL30
  | _ => []

/-- The cover slabs of band `i` (0-based) of atlas_50. -/
def lowerSlabs : Nat → List Slab
  | 0 => slabsL01
  | 1 => slabsL02
  | 2 => slabsL03
  | 3 => slabsL04
  | 4 => slabsL05
  | 5 => slabsL06
  | 6 => slabsL07
  | 7 => slabsL08
  | 8 => slabsL09
  | 9 => slabsL10
  | 10 => slabsL11
  | 11 => slabsL12
  | 12 => slabsL13
  | 13 => slabsL14
  | 14 => slabsL15
  | 15 => slabsL16
  | 16 => slabsL17
  | 17 => slabsL18
  | 18 => slabsL19
  | 19 => slabsL20
  | 20 => slabsL21
  | 21 => slabsL22
  | 22 => slabsL23
  | 23 => slabsL24
  | 24 => slabsL25
  | 25 => slabsL26
  | 26 => slabsL27
  | 27 => slabsL28
  | 28 => slabsL29
  | 29 => slabsL30
  | _ => []

end Erdos993Lean.Analytic.Atlas.Data
