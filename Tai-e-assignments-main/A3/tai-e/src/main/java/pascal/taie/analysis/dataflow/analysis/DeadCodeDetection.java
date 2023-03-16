/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // control-flow Unreachable
        LinkedList<Stmt> q = new LinkedList<>();
        HashSet<Stmt> visited = new HashSet<>();
        q.addLast(cfg.getEntry());

        while (!q.isEmpty())
        {
            Stmt stmt= q.pollFirst();
            if (visited.contains(stmt))
                continue;
            visited.add(stmt);

            Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(stmt);
            if (stmt instanceof If ifstmt
                    &&ConstantPropagation.evaluate(ifstmt.getCondition(),constants.getResult(ifstmt)).isConstant())
            {
                int res = ConstantPropagation.evaluate(ifstmt.getCondition(),constants.getResult(ifstmt)).getConstant();
                for (Edge<Stmt> edge:edges)
                {
                    if (edge.getKind()==Edge.Kind.IF_TRUE
                            &&res==1)
                        q.addLast(edge.getTarget());
                    else if (edge.getKind()==Edge.Kind.IF_FALSE
                            &&res==0)
                        q.addLast(edge.getTarget());
                }

            }
            else if (stmt instanceof SwitchStmt switchStmt
                    &&constants.getResult(switchStmt).get(switchStmt.getVar()).isConstant())
            {
                int res = constants.getResult(switchStmt).get(switchStmt.getVar()).getConstant();
                for (Edge<Stmt> edge:edges)
                {
                    if (edge.isSwitchCase()&&edge.getCaseValue()==res)
                    {
                        q.addLast(edge.getTarget());
                        break;
                    }
                }
                if (!switchStmt.getCaseValues().contains(res))
                    q.addLast(switchStmt.getDefaultTarget());
            }
            else if (stmt instanceof AssignStmt<?,?> assignStmt
                    && assignStmt.getLValue() instanceof Var var)
            {
                visited.remove(assignStmt);
                SetFact<Var> varSetFact = liveVars.getResult(assignStmt);
                // System.out.println(varSetFact);
                if (!hasNoSideEffect(assignStmt.getRValue())
                     || varSetFact.contains(var))
                {
                    visited.add(assignStmt);
                }

                for (Edge<Stmt> edge:edges)
                    q.addLast(edge.getTarget());
            }
            else
            {
                for (Edge<Stmt> edge:edges)
                {
                    if (!(edge.getKind()==Edge.Kind.CAUGHT_EXCEPTION))
                        q.addLast(edge.getTarget());
                }
            }
        }

        // System.out.println(visited);
        for (Stmt stmt:cfg.getNodes())
        {
            if (!visited.contains(stmt))
                deadCode.add(stmt);
        }

        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
