from z3 import *
import time
import xlwt

def SMT(n):
    Q = [Int('Q_ % i' % (i + 1)) for i in range(n)]
    val_c = [And(1 <= Q[i], Q[i] <= n) for i in range(n)]
    col_c = [Distinct(Q)]
    diag_c = [If(i == j, True,
                And(i + Q[i] != j + Q[j], i + Q[j] != j + Q[i]))
              for i in range(n) for j in range(i)]
    solver = Solver()
    solver.add(val_c + col_c + diag_c)

    start = time.time()
    if solver.check() == sat:
        model = solver.model()
        print(model)
    else:
        print(None)
    finish = time.time()
    return finish - start


def SAT(n):
    board = [[Bool("x_%s_%s" % (i, j)) for j in range(n)] for i in range(n)]
    # row constraints & column constraints
    constr = [Or([board[i][j] for j in range(n)]) for i in range(n)]
    constr += [Or(Not(board[i][j]), Not(board[i][k])) for i in range(n) for j in range(n) for k in range(j + 1, n)]
    constr += [Or([board[i][j] for i in range(n)]) for j in range(n)]
    constr += [Or(Not(board[i][j]), Not(board[k][j])) for j in range(n) for i in range(n) for k in range(i + 1, n)]
    # diagonal constraints
    for i in range(n):
        for ii in range(i + 1, n):
            for j in range(ii - i, n):
                jj = j - ii + i
                constr += [Or(Not(board[i][j]), Not(board[ii][jj]))]
            for j in range(n - ii + i):
                jj = j + ii - i
                constr += [Or(Not(board[i][j]), Not(board[ii][jj]))]

    solver = Solver()
    solver.add(constr)

    start = time.time()
    for k in range(1):
        if solver.check() == sat:
            model = solver.model()
            solution = []
            for i in range(n):
                for j in range(n):
                    if model[board[i][j]]:
                        solution += [j]
            print(solution)

            # 寻找其他解
            solver.add(Or([Not(board[i][solution[i]]) for i in range(n)]))
        else:
            print(None)
    finish = time.time()
    return finish - start

def time_w_constr():
    # 生成excel表格统计时间，范围1-30的nqueens问题
    workbook = xlwt.Workbook()
    sheet = workbook.add_sheet("time_w_constr")
    sheet.write(0, 0, "n")
    sheet.write(0, 1, "SMT")
    sheet.write(0, 2, "SAT")
    for i in range(1, 31):
        print("n = ", i)
        start1 = time.time()
        SMT(i)
        end1 = time.time()
        start2 = time.time()
        SAT(i)
        end2 = time.time()
        time1 = end1 - start1
        time2 = end2 - start2

        sheet.write(i, 0, i)
        sheet.write(i, 1, time1)
        sheet.write(i, 2, time2)
        workbook.save("time_w_constr.xls")

def time_wo_constr():
    # 生成excel表格统计时间，范围1-30的nqueens问题
    workbook = xlwt.Workbook()
    sheet = workbook.add_sheet("time_wo_constr")
    sheet.write(0, 0, "n")
    sheet.write(0, 1, "SMT")
    sheet.write(0, 2, "SAT")
    for i in range(1, 31):
        print("n = ", i)
        time1 = SMT(i)
        time2 = SAT(i)

        sheet.write(i, 0, i)
        sheet.write(i, 1, time1)
        sheet.write(i, 2, time2)
        workbook.save("time_wo_constr.xls")

if __name__ == '__main__':
    time_w_constr()
    time_wo_constr()