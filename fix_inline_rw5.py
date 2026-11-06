import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    "            simp only [hframes_m6] at h_get_rest\n            dsimp [Array.back?] at h_get_rest\n            dsimp [pure, EStateM.pure] at h_get_rest\n",
    "            rw [hframes_m6] at h_get_rest\n            change EStateM.Result.ok topFrame6 m6 = EStateM.Result.ok res_f2 m8 at h_get_rest\n"
)
content = content.replace(
    "| error e =>\n              simp only [Array.size_toArray, List.length, Nat.sub_self, Array.getElem_toArray, List.getElem_singleton, getElem] at h_sl\n              trace_state\n              rw [h_set_op] at h_sl",
    "| error e =>\n              rw [h_set_op] at h_sl"
)
content = content.replace(
    "| ok frame_new =>\n              simp only [Array.size_toArray, List.length, Nat.sub_self, Array.getElem_toArray, List.getElem_singleton, getElem] at h_sl\n              rw [h_set_op] at h_sl",
    "| ok frame_new =>\n              rw [h_set_op] at h_sl"
)

with open(path, "w") as f:
    f.write(content)
