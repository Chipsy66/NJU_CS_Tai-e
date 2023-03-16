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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (!callGraph.contains(csMethod))
        {
            callGraph.addReachableMethod(csMethod);
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for (Stmt stmt:csMethod.getMethod().getIR().getStmts())
            {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            CSVar csVar = csManager.getCSVar(context,stmt.getLValue());
            Context selectHeapContext = contextSelector.selectHeapContext(csMethod,heapModel.getObj(stmt));
            workList.addEntry(csVar,PointsToSetFactory.make(csManager.getCSObj(selectHeapContext,heapModel.getObj(stmt))));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar csVar_left = csManager.getCSVar(context,stmt.getLValue());
            CSVar csVar_right = csManager.getCSVar(context,stmt.getRValue());
            addPFGEdge(csVar_right,csVar_left);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic())
            {
                CSVar csVar_src = csManager.getCSVar(context,stmt.getRValue());
                StaticField staticField_tgt = csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                addPFGEdge(csVar_src,staticField_tgt);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic())
            {
                CSVar csVar_tgt = csManager.getCSVar(context,stmt.getLValue());
                StaticField staticField_src = csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                addPFGEdge(staticField_src,csVar_tgt);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic())
            {
                JMethod jMethod = resolveCallee(null,stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                CSMethod csMethod = csManager.getCSMethod(contextSelector.selectContext(csCallSite, jMethod), jMethod);
                if (!callGraph.getCalleesOf(csCallSite).contains(csMethod))
                {
                    callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csMethod));
                    processInvoke(csCallSite, csMethod);
                }
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
                workList.addEntry(target, source.getPointsToSet());
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
            if (n instanceof CSVar csVar)
            {
                for (CSObj csObj:delta)
                {
                    for (LoadField loadField:csVar.getVar().getLoadFields())
                    {
                        // x = y.f
                        InstanceField instanceField_src = csManager.getInstanceField(csObj,loadField.getFieldAccess().getFieldRef().resolve());
                        CSVar csVar_tgt = csManager.getCSVar(csVar.getContext(), loadField.getLValue());
                        addPFGEdge(instanceField_src,csVar_tgt);
                    }
                    for (StoreField storeField:csVar.getVar().getStoreFields())
                    {
                        // x.f = y
                        InstanceField instanceField_tgt = csManager.getInstanceField(csObj,storeField.getFieldAccess().getFieldRef().resolve());
                        CSVar csVar_src = csManager.getCSVar(csVar.getContext(), storeField.getRValue());
                        addPFGEdge(csVar_src,instanceField_tgt);
                    }
                    for (LoadArray loadArray:csVar.getVar().getLoadArrays())
                    {
                        ArrayIndex arrayIndex_src = csManager.getArrayIndex(csObj);
                        CSVar csVar_tgt = csManager.getCSVar(csVar.getContext(), loadArray.getLValue());
                        addPFGEdge(arrayIndex_src,csVar_tgt);
                    }
                    for (StoreArray storeArray:csVar.getVar().getStoreArrays())
                    {
                        ArrayIndex arrayIndex_tgt = csManager.getArrayIndex(csObj);
                        CSVar csVar_src = csManager.getCSVar(csVar.getContext(), storeArray.getRValue());
                        addPFGEdge(csVar_src,arrayIndex_tgt);
                    }
                    processCall(csVar,csObj);
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
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj obj:pointsToSet)
        {
            if (!ptn.contains(obj))
            {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty())
        {
            for (CSObj obj:delta)
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke invoke:recv.getVar().getInvokes())
        {
            JMethod method = resolveCallee(recvObj,invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context context = contextSelector.selectContext(csCallSite,recvObj,method); // 𝑐^𝑡 = Select(𝑐, 𝑙, 𝑐′:𝑜_𝑖)
            CSVar c_t_m_this = csManager.getCSVar(context, method.getIR().getThis());
            workList.addEntry(c_t_m_this, PointsToSetFactory.make(recvObj));
            CSMethod csMethod = csManager.getCSMethod(context, method);
            if (!callGraph.getCalleesOf(csCallSite).contains(csMethod))
            {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod));
                processInvoke(csCallSite, csMethod);
            }
        }
    }

    private void processInvoke(CSCallSite csCallSite, CSMethod csMethod) {
        addReachable(csMethod);
        for (int i=0; i<csMethod.getMethod().getParamCount();i++)
        {
            CSVar src = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getInvokeExp().getArg(i));
            CSVar tgt = csManager.getCSVar(csMethod.getContext(), csMethod.getMethod().getIR().getParam(i));
            addPFGEdge(src, tgt);
        }
        for (Var returnVar:csMethod.getMethod().getIR().getReturnVars())
        {
            if (csCallSite.getCallSite().getLValue()!=null)
            {
                CSVar return_src = csManager.getCSVar(csMethod.getContext(), returnVar);
                CSVar csVar_tgt = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getLValue());
                addPFGEdge(return_src, csVar_tgt);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
