import Stafford38.Geometry.PaperSameWitnessTangentDimension

set_option autoImplicit false

-- The bound's finite-dimensional hypotheses and completed point are covered
-- by the independent proof audit; this probe checks its imported axiom closure.
#check Stafford38.Geometry.PaperSameWitnessTangentDimension.tangent_finrank_goal
#check Stafford38.Geometry.PaperSameWitnessTangentDimension.tangent_finrank_le_residue_add_one_of_witness
#print axioms Stafford38.Geometry.PaperSameWitnessTangentDimension.tangent_finrank_le_residue_add_one_of_witness
