import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem solution {F : Type*} [CommRing F] (matrixTerm ds gl ur ed m : F) :
    (ds+ed+m)-((matrixTerm+ds+gl)-(matrixTerm+ur))=m+ed-gl+ur := by ring
