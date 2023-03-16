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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.LinkedList;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method))
        {
            callGraph.addReachableMethod(method);
            for (Stmt stmt: method.getIR().getStmts())
            {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Pointer pointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
            PointsToSet pointsToSet = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(pointer,pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer src = pointerFlowGraph.getVarPtr(stmt.getRValue());
            Pointer tgt = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(src,tgt);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic())
            {
                JMethod method = resolveCallee(null,stmt);
                callGraph.getCalleesOf(stmt);
                if (!callGraph.getCalleesOf(stmt).contains(method))
                {
                    callGraph.addEdge(new Edge<>(CallKind.STATIC,stmt,method));
                    processInvoke(stmt, method);
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic())
            {
                Pointer src = pointerFlowGraph.getVarPtr(stmt.getRValue());
                Pointer tgt = pointerFlowGraph.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                addPFGEdge(src,tgt);
            }

            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic())
            {
                Pointer src = pointerFlowGraph.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                Pointer tgt = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(src,tgt);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (!pointerFlowGraph.getSuccsOf(source).contains(target))
        {
            pointerFlowGraph.addEdge(source,target);
            if (!source.getPointsToSet().isEmpty())
            {
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty())
        {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(n,pts);
            if (n instanceof VarPtr varPtr)
            {
                for (Obj obj:delta)
                {
                    for (LoadField loadField:varPtr.getVar().getLoadFields())
                    {
                        Pointer src = pointerFlowGraph.getInstanceField(obj,loadField.getFieldAccess().getFieldRef().resolve());
                        Pointer tgt = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        addPFGEdge(src,tgt);
                    }
                    for (StoreField storeField:varPtr.getVar().getStoreFields())
                    {
                        Pointer src = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        Pointer tgt = pointerFlowGraph.getInstanceField(obj,storeField.getFieldAccess().getFieldRef().resolve());
                        addPFGEdge(src,tgt);
                    }
                    for (LoadArray loadArray:varPtr.getVar().getLoadArrays())
                    {
                        Pointer src = pointerFlowGraph.getArrayIndex(obj);
                        Pointer tgt = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        addPFGEdge(src,tgt);
                    }
                    for (StoreArray storeArray:varPtr.getVar().getStoreArrays())
                    {
                        Pointer src = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        Pointer tgt = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(src,tgt);
                    }
                    processCall(varPtr.getVar(),obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet delta = new PointsToSet();
        for (Obj obj:pointsToSet)
        {
            if (!ptn.contains(obj))
            {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty())
        {
            for (Obj obj:delta)
            {
                ptn.addObject(obj);
            }
            for (Pointer s:pointerFlowGraph.getSuccsOf(pointer))
            {
                workList.addEntry(s,delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke:var.getInvokes())
        {
            JMethod method = resolveCallee(recv,invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()),new PointsToSet(recv));
            if (!callGraph.getCalleesOf(invoke).contains(method))
            {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,method));
                processInvoke(invoke, method);
            }
        }
    }

    public void processInvoke(Invoke invoke, JMethod method) {
        addReachable(method);
        for (int i=0;i<method.getParamCount();i++)
        {
            Pointer src = pointerFlowGraph.getVarPtr(invoke.getRValue().getArg(i));
            Pointer tgt = pointerFlowGraph.getVarPtr(method.getIR().getParam(i));
            addPFGEdge(src,tgt);
        }
        for (Var returnVar : method.getIR().getReturnVars())
        {
            if (invoke.getLValue() != null)
            {
                Pointer src = pointerFlowGraph.getVarPtr(returnVar);
                Pointer tgt = pointerFlowGraph.getVarPtr(invoke.getLValue());
                addPFGEdge(src,tgt);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
