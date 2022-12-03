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
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Set;

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

    public CSCallGraph getCallGraph() { return callGraph; }

    public Set<Pointer> getSuccsOf(Pointer pointer) {
        return pointerFlowGraph.getSuccsOf(pointer);
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
        if (callGraph.contains(csMethod)) return;

        callGraph.addReachableMethod(csMethod);
        csMethod.getMethod().getIR().forEach(s -> s.accept(new StmtProcessor(csMethod)));
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

        @Override
        public Void visit(New stmt) {
            Pointer pointer = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(heapContext, obj);
            workList.addEntry(pointer, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer target = csManager.getCSVar(context, stmt.getLValue());
            Pointer source = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(source, target);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                Pointer target = csManager.getStaticField(stmt.getFieldRef().resolve());
                Pointer source = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Pointer target = csManager.getCSVar(context, stmt.getLValue());
                Pointer source = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public  Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context methodContext = contextSelector.selectContext(csCallSite, callee);
                addReachable(csManager.getCSMethod(methodContext, callee));
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                    Pointer target = csManager.getCSVar(methodContext, callee.getIR().getParam(i));
                    Pointer source = csManager.getCSVar(context, stmt.getInvokeExp().getArg(i));
                    addPFGEdge(source, target);
                }
                if (stmt.getLValue() != null) {
                    Pointer target = csManager.getCSVar(context, stmt.getLValue());
                    for (Var ret : callee.getIR().getReturnVars()) {
                        Pointer source = csManager.getCSVar(methodContext, ret);
                        addPFGEdge(source, target);
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target)) return;

        if (!source.getPointsToSet().isEmpty())
            workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry e = workList.pollEntry();
            PointsToSet diff = propagate(e.pointer(), e.pointsToSet());
            if (!diff.isEmpty() && e.pointer() instanceof CSVar csVar) {
                for (CSObj csObj : diff.getObjects()) {
                    for (StoreField stmt : csVar.getVar().getStoreFields()) {
                        Pointer target = csManager.getInstanceField(csObj, stmt.getFieldRef().resolve());
                        Pointer source = csManager.getCSVar(csVar.getContext(), stmt.getRValue());
                        addPFGEdge(source, target);
                    }
                    for (LoadField stmt : csVar.getVar().getLoadFields()) {
                        Pointer target = csManager.getCSVar(csVar.getContext(), stmt.getLValue());
                        Pointer source = csManager.getInstanceField(csObj, stmt.getFieldRef().resolve());
                        addPFGEdge(source, target);
                    }
                    for (StoreArray stmt : csVar.getVar().getStoreArrays()) {
                        Pointer target = csManager.getArrayIndex(csObj);
                        Pointer source = csManager.getCSVar(csVar.getContext(), stmt.getRValue());
                        addPFGEdge(source, target);
                    }
                    for (LoadArray stmt : csVar.getVar().getLoadArrays()) {
                        Pointer target = csManager.getCSVar(csVar.getContext(), stmt.getLValue());
                        Pointer source = csManager.getArrayIndex(csObj);
                        addPFGEdge(source, target);
                    }
                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diff = PointsToSetFactory.make();
        pointsToSet.objects().filter(p -> !pointer.getPointsToSet().contains(p)).forEach(diff::addObject);

        if (!diff.isEmpty()) {
            diff.objects().forEach(pointer.getPointsToSet()::addObject);
            pointerFlowGraph.getSuccsOf(pointer).forEach(t -> workList.addEntry(t, diff));
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke stmt : recv.getVar().getInvokes()) {
            if (stmt.isStatic()) continue;
            JMethod callee = resolveCallee(recvObj, stmt);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), stmt);
            Context methodContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csMethod = csManager.getCSMethod(methodContext, callee);
            workList.addEntry(csManager.getCSVar(methodContext, callee.getIR().getThis()), PointsToSetFactory.make(recvObj));
            addReachable(csMethod);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csMethod))) {
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                    Pointer target = csManager.getCSVar(methodContext, callee.getIR().getParam(i));
                    Pointer source = csManager.getCSVar(recv.getContext(), stmt.getInvokeExp().getArg(i));
                    addPFGEdge(source, target);
                }
                if (stmt.getLValue() != null) {
                    Pointer target = csManager.getCSVar(recv.getContext(), stmt.getLValue());
                    for (Var ret : callee.getIR().getReturnVars()) {
                        Pointer source = csManager.getCSVar(methodContext, ret);
                        addPFGEdge(source, target);
                    }
                }
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
