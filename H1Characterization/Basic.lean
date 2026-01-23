import Foundations.Cohomology
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace H1Characterization

export Foundations (Coeff Vertex sign Simplex SimplicialComplex Cochain coboundary)
export Foundations (IsCocycle IsCoboundary H1Trivial delta_sq_zero)

-- Re-export Simplex.vertex so it's available without namespace prefix
open Foundations.Simplex (vertex) in
export Foundations.Simplex (vertex)

end H1Characterization
