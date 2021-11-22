import retypd
import sys
import argparse
import itertools
import re

if __name__ == "__main__":
    app = argparse.ArgumentParser(
        "Solve a set of constraints in terms of interesting type vars")

    app.add_argument("constraints", type=argparse.FileType('r'))
    app.add_argument("--interesting_tvars", type=argparse.FileType('r'))

    args = app.parse_args()

    cons_set = retypd.ConstraintSet([retypd.SchemaParser.parse_constraint(line)
                                     for line in args.constraints])

    if args.interesting_tvars:
        interesting_tvars = [line for line in args.interesting_tvars]
    else:
        all_dt = list(itertools.chain.from_iterable((cons.left, cons.right)
                      for cons in cons_set.subtype))
        interesting_tvars = [cons.base for cons in all_dt if len(cons.path) > 0 and (isinstance(
            cons.path[0], retypd.InLabel) or isinstance(cons.path[0], retypd.OutLabel))]

        # interesting_tvars += [cons.base for cons in all_dt if re.fullmatch(
        #    "sub_[\da-z]*@sp", cons.base)]

    print(interesting_tvars)
    solver = retypd.Solver(cons_set, interesting_tvars)
    print(cons_set)
    solver()

    for cons in solver.constraints:
        print(cons)
