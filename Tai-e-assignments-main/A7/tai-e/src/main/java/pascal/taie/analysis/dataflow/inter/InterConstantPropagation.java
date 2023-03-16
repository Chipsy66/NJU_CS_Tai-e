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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    public PointerAnalysisResult pta;
    public DataflowResult factDataflowResult;

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        this.pta = World.get().getResult(ptaId);
        // TODO : You can do initialization work here
//        pta.getVars().forEach(var -> {
//            if ()
//        });
        //this.factDataflowResult = this.solver.getDataFlowResult();
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact in_copy = in.copy();
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            if (definitionStmt instanceof StoreArray storeArray) {
                // a[i] = x
                Var base = storeArray.getArrayAccess().getBase();
                Var offset = storeArray.getArrayAccess().getIndex();
                CPFact cpFact_curr = this.solver.getDataFlowResult().getOutFact(storeArray);
                pta.getVars().forEach(var -> {
                    if (checkBase(base, var)) {
                        var.getLoadArrays().forEach(loadArray -> {
                            CPFact cpFact_loadToCurr = this.solver.getDataFlowResult().getOutFact(loadArray).copy();
                            Var index = loadArray.getArrayAccess().getIndex();
                            Value value = cpFact_loadToCurr.get(index);
                            if (checkArrayIndex(cpFact_curr.get(offset), value)) {
                                this.solver.addWorkList(loadArray);
                            }

                        });
                    }
                });
                return cp.transferNode(stmt, in, out);
            }
            if (definitionStmt instanceof LoadArray loadArray) {
                //  x=a[i]
                Var base = loadArray.getArrayAccess().getBase();
                Var offset = loadArray.getArrayAccess().getIndex();
                CPFact cpFact_curr = this.solver.getDataFlowResult().getOutFact(loadArray);
                AtomicReference<Value> value = new AtomicReference<>(Value.getUndef());
                pta.getVars().forEach(var -> {
                    if (checkBase(base, var)) {
                        var.getStoreArrays().forEach(storeArray -> {
                            CPFact cpFact_storeToCurr = solver.getDataFlowResult().getOutFact(storeArray);
                            Var index = storeArray.getArrayAccess().getIndex();

                            Value store_R_value = cpFact_storeToCurr.get(storeArray.getRValue());
                            if (checkArrayIndex(cpFact_storeToCurr.get(index), cpFact_curr.get(offset))) {
                                value.set(this.cp.meetValue(value.get(), store_R_value));
                            }
                        });
                    }
                });
                out.copyFrom(in_copy);
                CPFact out_origin = out.copy();
                out.update(loadArray.getLValue(), value.get());
                return !out.equals(out_origin);
            }
            if (definitionStmt instanceof StoreField storeField) {
                if (storeField.isStatic()) {
                    // A.f = b;
                    JClass A = storeField.getFieldAccess().getFieldRef().getDeclaringClass();
                    JField f = storeField.getFieldAccess().getFieldRef().resolve();

                    icfg.forEach(stmt_ -> {
                        if (checkSame(stmt_, f, A) && stmt_ instanceof LoadField) {
                            solver.addWorkList(stmt_);
                        }
                    });
                } else {// a.f = b;

                    JClass a = storeField.getFieldAccess().getFieldRef().getDeclaringClass();
                    if (storeField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                        Var base = instanceFieldAccess.getBase();
                        JField f = storeField.getFieldAccess().getFieldRef().resolve();
                        CPFact cpFact_curr = this.solver.getDataFlowResult().getOutFact(storeField);
                        pta.getVars().forEach(var -> {
                            if (checkBase(base, var)) {
                                var.getLoadFields().forEach(loadField -> {
                                    if (loadField.getFieldAccess().getFieldRef().resolve() == f
                                            && !loadField.isStatic()) {
                                        solver.addWorkList(loadField);
                                    }
                                });
                            }
                        });
                    }
                }
                cp.transferNode(stmt, in, out);
            }
            if (definitionStmt instanceof LoadField loadField) {
                AtomicReference<Value> value = new AtomicReference<>(Value.getUndef());
                if (loadField.isStatic()) {
                    // b = A.f;
                    JClass A = loadField.getFieldAccess().getFieldRef().getDeclaringClass();
                    JField f = loadField.getFieldAccess().getFieldRef().resolve();
                    icfg.forEach(stmt_ -> {
                        if (checkSame(stmt_, f, A)) {
                            if (stmt_ instanceof StoreField storeField) {
                                CPFact cpFact = solver.getDataFlowResult().getOutFact(storeField);
                                value.set(cp.meetValue(value.get(), cpFact.get(storeField.getRValue())));
                            }

                        }
                    });

                } else {
                    // b = a.f;
                    JClass a = loadField.getFieldAccess().getFieldRef().getDeclaringClass();
                    if (loadField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                        Var base = instanceFieldAccess.getBase();
                        JField f = loadField.getFieldAccess().getFieldRef().resolve();

                        pta.getVars().forEach(var -> {
                            if (checkBase(base, var)) {
                                var.getStoreFields().forEach(storeField -> {
                                    if (storeField.getFieldAccess().getFieldRef().resolve() == f
                                            && !storeField.isStatic()) {
                                        CPFact cpFact = solver.getDataFlowResult().getOutFact(storeField);
                                        value.set(cp.meetValue(value.get(), cpFact.get(storeField.getRValue())));
                                    }
                                });
                            }
                        });
                    }

                }
                out.copyFrom(in_copy);
                CPFact out_origin = out.copy();
                out.update(loadField.getLValue(), value.get());
                return !out.equals(out_origin);
            }

        }
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact copy = out.copy();
        if (edge.getSource() instanceof Invoke invoke/*DefinitionStmt definitionStmt*/
                && invoke.getDef().isPresent()) {
            // copy.remove(var);
            copy.update(invoke.getLValue(), Value.getUndef());
        }
        return copy;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact copy = new CPFact();
        List<Var> params = edge.getCallee().getIR().getParams();
        if (edge.getSource() instanceof Invoke invoke) {
            InvokeExp invokeExp = invoke.getInvokeExp();
            for (int i = 0; i < params.size(); i++) {
                Var param = params.get(i);
                copy.update(param, callSiteOut.get(invokeExp.getArg(i)));
            }
        }
        return copy;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact copy = new CPFact();
        if (edge.getCallSite() instanceof Invoke invoke
                && invoke.getLValue() == null)
            return copy;

        if (edge.getCallSite() instanceof Invoke invoke
                && invoke.getLValue() != null) {
            Value value = Value.getUndef();
            Collection<Var> returns = edge.getReturnVars();
            for (Var var : returns) {
                value = cp.meetValue(value, returnOut.get(var));
            }
            copy.update(invoke.getLValue(), value);
        }
        return copy;
    }

    protected boolean checkBase(Var lVar, Var rVar) {
        for (Obj obj : pta.getPointsToSet(lVar)) {
            if (pta.getPointsToSet(rVar).contains(obj))
                return true;
        }
        return false;
    }

    protected boolean checkArrayIndex(Value lValue, Value rValue) {
        if (lValue.isConstant() && rValue.isConstant()) {
            return lValue.getConstant() == rValue.getConstant();
        }
        return !lValue.isUndef() && !rValue.isUndef();
    }

    protected boolean checkSame(Stmt stmt, JField jField, JClass jClass) {
        return (stmt instanceof LoadField loadField
                && loadField.isStatic()
                && loadField.getFieldAccess().getFieldRef().getDeclaringClass() == jClass
                && loadField.getFieldAccess().getFieldRef().resolve() == jField
        )
                ||
                (stmt instanceof StoreField storeField
                        && storeField.isStatic()
                        && storeField.getFieldAccess().getFieldRef().getDeclaringClass() == jClass
                        && storeField.getFieldAccess().getFieldRef().resolve() == jField
                )
                ;
    }
}
