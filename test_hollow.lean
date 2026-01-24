import Perspective.AlignmentEquivalence

-- Test: Can we compute faces on concrete simplices?
#check @Foundations.Simplex.face
#check @Foundations.coboundary

-- Try to compute face on {0, 1}
example : ({0, 1} : Foundations.Simplex).card = 2 := by native_decide
example : Foundations.Simplex.face {0, 1} ⟨0, by native_decide⟩ = {1} := by native_decide
example : Foundations.Simplex.face {0, 1} ⟨1, by native_decide⟩ = {0} := by native_decide

-- Similarly for {1, 2}
example : Foundations.Simplex.face {1, 2} ⟨0, by native_decide⟩ = {2} := by native_decide
example : Foundations.Simplex.face {1, 2} ⟨1, by native_decide⟩ = {1} := by native_decide

-- And {0, 2}
example : Foundations.Simplex.face {0, 2} ⟨0, by native_decide⟩ = {2} := by native_decide
example : Foundations.Simplex.face {0, 2} ⟨1, by native_decide⟩ = {0} := by native_decide

-- Sign computations
example : Foundations.sign 0 = 1 := Foundations.sign_zero
example : Foundations.sign 1 = -1 := Foundations.sign_one
