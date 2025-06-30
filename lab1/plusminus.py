from z3 import *

def minus():
    bits = 4
    # d = a - b
    a_num = 8
    b_num = 3
    d_num = 0

    a = [Bool("a_%s" % i) for i in range(bits)]
    b = [Bool("b_%s" % i) for i in range(bits)]
    d = [Bool("d_%s" % i) for i in range(bits)]

    carry = [Bool("c_%s" % i) for i in range(bits + 1)]

    constr = [a[i] == (b[i] == (d[i] == carry[i])) for i in range(bits)]
    constr += [carry[i + 1] == (Or(And(b[i], d[i]), And(b[i], carry[i]), And(d[i], carry[i]))) for i in range(bits)]
    constr += [Not(carry[bits])]
    constr += [Not(carry[0])]
    for i in range(bits):
        if b_num & (1 << i):
            constr += [b[i]]
        else:
            constr += [Not(b[i])]
        if a_num & (1 << i):
            constr += [a[i]]
        else:
            constr += [Not(a[i])]

    solver = Solver()
    solver.add(constr)
    if solver.check() == sat:
        m = solver.model()
        for i in range (bits):
            if m[d[i]]:
                d_num += 1 << i
        print("d_num = %s" % d_num)

if __name__ == '__main__':
    minus()
