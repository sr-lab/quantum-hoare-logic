import numpy as np
from fractions import Fraction

st = input("expression: ")
name = input("name: ")

I = np.eye(2)
CNOT = np.array([[1, 0, 0, 0],
                 [0, 1, 0, 0],
                 [0, 0, 0, 1],
                 [0, 0, 1, 0]])
X = np.array([[0, 1],
              [1, 0]])
H = (1 / np.sqrt(2)) * np.array([[1, 1],
                                 [1,-1]])
Z = np.array([[1, 0],
              [0, -1]])
q0 = np.array([1, 0]).reshape(1, -1)
q1 = np.array([0, 1]).reshape(1, -1)

m0 = q0.T.dot(q0)
m1 = q1.T.dot(q1)

def parse(st):
    mults = [s.strip() for s in st.split("×")]
    exps = []
    for m in mults:
        exps.append(m.split("⊗"))
    return mult_all(exps)

def recur(exp):
    if len(exp) == 0:
        return 1
    if "I 2" in exp[0]:
        return np.kron(I, recur(exp[1:]))
    if "X" in exp[0]:
        return np.kron(X, recur(exp[1:]))
    if "H" in exp[0]:
        return np.kron(H, recur(exp[1:]))
    if "Z" in exp[0]:
        return np.kron(Z, recur(exp[1:]))
    if "CNOT" in exp[0]:
        return np.kron(CNOT, recur(exp[1:]))
    if "∣0⟩⟨0∣" in exp[0]:
        return np.kron(q0.T.dot(q0), recur(exp[1:]))
    if "∣ 0 ⟩" in exp[0] or "∣0⟩" in exp[0]:
        return np.kron(q0, recur(exp[1:]))
    if "⟨ 0 ∣" in exp[0] or "⟨0∣" in exp[0]:
        return np.kron(q0.T, recur(exp[1:]))

def mult_all(exps):
    if len(exps) == 1:
        return recur(exps[0])
    return recur(exps[0]).dot(mult_all(exps[1:]))

def transform_matrix_to_coq_form(mat):
    res = "l2M ["
    for row in mat:
        st = "["
        for e in row:
            st += str(Fraction("{:.1f}".format(e))) + ";"
        st = st[:-1] + "];\n"
        res += st
    res = res[:-2] + "]"
    return res

def generate_lemma(st, name):
    mat = parse(st)
    lemma = """
Lemma {}: {} = {}.
Proof.
(* BY PYTHON SCRIPT *)
Admitted.
""".format(name, st, transform_matrix_to_coq_form(mat))
    return lemma
    
print(generate_lemma(st, name))
