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

package pascal.taie.analysis.dataflow.analysis.constprop;

import com.fasterxml.jackson.databind.annotation.JsonPOJOBuilder;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact temp = new CPFact();
        for (Var var : cfg.getIR().getParams())
        {
            if (canHoldInt(var))
            {
                temp.update(var, Value.getNAC());
            }
        }
        return temp;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var:fact.keySet())
        {
            target.update(var,meetValue(fact.get(var),target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        if (v1.isUndef() && v2.isUndef())
            return Value.getUndef();
        if (v1.isConstant() && v2.isConstant())
        {
            return v1.getConstant() == v2.getConstant()
                    ? Value.makeConstant(v1.getConstant()) : Value.getNAC();
        }
        return v1.isUndef() ? v2 : v1;

    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact temp = in.copy();
        if (stmt instanceof DefinitionStmt<?,?> definitionStmt)
        {
            if (definitionStmt.getLValue() instanceof Var var
                    && definitionStmt.getRValue() != null
                    && canHoldInt(var))
            {
                temp.remove(var);
                boolean res = out.copyFrom(temp);
                res |= out.update(var, evaluate(definitionStmt.getRValue(), in));
                return res;
            }
        }
        return out.copyFrom(temp);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me

        if (exp instanceof IntLiteral intLiteral)
            return Value.makeConstant(intLiteral.getValue());

        if (exp instanceof Var var)
            return in.get(var);

        if (exp instanceof BinaryExp binaryExp)
        {
            Value op1 = in.get(binaryExp.getOperand1());
            Value op2 = in.get(binaryExp.getOperand2());

            if (op2.isConstant()&&op2.getConstant()==0
                    &&binaryExp instanceof ArithmeticExp arithmeticExp)
            {
                if (arithmeticExp.getOperator()== ArithmeticExp.Op.DIV
                        ||arithmeticExp.getOperator()== ArithmeticExp.Op.REM)
                    return Value.getUndef();
            }
            if (op1.isNAC()
                    ||op2.isNAC())
            {
                return Value.getNAC();
            }

            if (op1.isConstant()
                    &&op2.isConstant())
            {
                if (binaryExp instanceof ArithmeticExp arithmeticExp)
                {
                    switch (arithmeticExp.getOperator())
                    {
                        case ADD -> {
                            return Value.makeConstant(
                                    op1.getConstant() + op2.getConstant());
                        }
                        case SUB -> {
                            return Value.makeConstant(
                                    op1.getConstant() - op2.getConstant());
                        }
                        case MUL -> {
                            return Value.makeConstant(
                                    op1.getConstant() * op2.getConstant());
                        }
                        case DIV -> {
                            if (op2.getConstant()==0)
                                return Value.getUndef();
                            return Value.makeConstant(
                                    op1.getConstant() / op2.getConstant());
                        }
                        case REM -> {
                            if (op2.getConstant()==0)
                                return Value.getUndef();
                            return Value.makeConstant(
                                    op1.getConstant() % op2.getConstant());
                        }
                    }
                }
                else if (binaryExp instanceof ConditionExp conditionExp)
                {
                    switch (conditionExp.getOperator())
                    {
                        case EQ -> {
                            return Value.makeConstant(
                                    op1.getConstant() == op2.getConstant() ? 1 : 0 );
                        }
                        case GE -> {
                            return Value.makeConstant(
                                    op1.getConstant() >= op2.getConstant() ? 1 : 0 );
                        }
                        case GT -> {
                            return Value.makeConstant(
                                    op1.getConstant() > op2.getConstant() ? 1 : 0 );
                        }
                        case LE -> {
                            return Value.makeConstant(
                                    op1.getConstant() <= op2.getConstant() ? 1 : 0 );
                        }
                        case LT -> {
                            return Value.makeConstant(
                                    op1.getConstant() < op2.getConstant() ? 1 : 0 );
                        }
                        case NE -> {
                            return Value.makeConstant(
                                    op1.getConstant() != op2.getConstant() ? 1 : 0 );
                        }

                    }
                }
                else if (binaryExp instanceof ShiftExp shiftExp)
                {
                    switch (shiftExp.getOperator())
                    {
                        case SHL -> {
                            return Value.makeConstant(
                                    op1.getConstant() << op2.getConstant());
                        }
                        case SHR -> {
                            return Value.makeConstant(
                                    op1.getConstant() >> op2.getConstant());
                        }
                        case USHR -> {
                            return Value.makeConstant(
                                    op1.getConstant() >>> op2.getConstant());
                        }
                    }
                }
                else if (binaryExp instanceof BitwiseExp bitwiseExp)
                {
                    switch (bitwiseExp.getOperator())
                    {
                        case OR -> {
                            return Value.makeConstant(
                                    op1.getConstant() | op2.getConstant());
                        }
                        case AND -> {
                            return Value.makeConstant(
                                    op1.getConstant() & op2.getConstant());
                        }
                        case XOR -> {
                            return Value.makeConstant(
                                    op1.getConstant() ^ op2.getConstant());
                        }
                    }
                }
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
