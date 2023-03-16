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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        LinkedList<JMethod> q = new LinkedList<>();
        q.addLast(entry);

        while (!q.isEmpty())
        {
            JMethod m = q.pollFirst();
            if (!callGraph.contains(m))
            {
                callGraph.addReachableMethod(m);
                callGraph.callSitesIn(m).forEach(callSite-> {
                    Set<JMethod> t = resolve(callSite);
                    t.forEach(jMethod-> {
                        callGraph.addEdge(
                                new Edge<>(CallGraphs.getCallKind(callSite),callSite,jMethod));
                        q.addLast(jMethod);
                    });
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> methodSet = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        JClass jClass = methodRef.getDeclaringClass();
        if (CallGraphs.getCallKind(callSite)==CallKind.STATIC)
        {
            JMethod toAdd = jClass.getDeclaredMethod(subsignature);
            if (toAdd!=null)
                methodSet.add(toAdd);
            return methodSet;
        }
        else if (CallGraphs.getCallKind(callSite)==CallKind.SPECIAL)
        {
            JMethod toAdd = dispatch(jClass,subsignature);
            if (toAdd!=null)
                methodSet.add(toAdd);
            return methodSet;
        }
        else if (CallGraphs.getCallKind(callSite)==CallKind.VIRTUAL
                   ||CallGraphs.getCallKind(callSite)==CallKind.INTERFACE)
        {
            LinkedList<JClass> q = new LinkedList<>();
            q.addLast(jClass);
            while (!q.isEmpty())
            {
                JClass curr = q.pollFirst();

                JMethod toAdd = dispatch(curr,subsignature);
                if (toAdd!=null)
                    methodSet.add(toAdd);

                if (curr.isInterface())
                {
                    q.addAll(hierarchy.getDirectImplementorsOf(curr));
                    q.addAll(hierarchy.getDirectSubinterfacesOf(curr));
                }
                else
                {
                    q.addAll(hierarchy.getDirectSubclassesOf(curr));
                }
            }
            return methodSet;
        }
        return methodSet;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass==null)
            return null;

        JMethod thisMethod = jclass.getDeclaredMethod(subsignature);
        if (thisMethod!=null
                &&!thisMethod.isAbstract())
            return thisMethod;

        JClass superClass = jclass.getSuperClass();
        if (superClass==null)
            return null;

        return dispatch(superClass,subsignature);
    }
}
