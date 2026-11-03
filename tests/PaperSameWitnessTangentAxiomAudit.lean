module
public import Stafford38.Geometry.PaperSameWitnessTangentDimension

@[expose] public section

set_option autoImplicit false

-- This probe checks the imported axiom closure of the bound.
#check Stafford38.Geometry.PaperSameWitnessTangentDimension.tangent_finrank_goal
#check Stafford38.Geometry.PaperSameWitnessTangentDimension.tangent_finrank_le_residue_add_one_of_witness
#print axioms Stafford38.Geometry.PaperSameWitnessTangentDimension.tangent_finrank_le_residue_add_one_of_witness
