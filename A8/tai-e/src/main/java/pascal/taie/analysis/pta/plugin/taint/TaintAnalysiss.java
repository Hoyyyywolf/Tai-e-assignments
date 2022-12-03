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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Sets;

import java.util.*;
import java.util.stream.Stream;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private CSCallGraph callGraph;

    private List<Invoke> allInvokes;

    private WorkList workList;

    private PointerAnalysisResult ptaResult;

    private Map<Pointer, PointsToSet> taintResult;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        workList = new WorkList();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        ptaResult = solver.getResult();
        callGraph = solver.getCallGraph();
        taintResult = new HashMap<>();
        allInvokes = callGraph
                .reachableMethods()
                .map(CSMethod::getMethod)
                .distinct()
                .flatMap(m -> m.getIR().getStmts().stream())
                .filter(stmt -> stmt instanceof Invoke)
                .map(stmt -> (Invoke)stmt)
                .toList();

        addSourceTaint();
        analyze();
        checkTaints(taintFlows);

        return taintFlows;
    }

    private PointsToSet getTaintPtsOfPointer(Pointer pointer) {
        if (!taintResult.containsKey(pointer)) {
            taintResult.put(pointer, new PointsToSet());
        }
        return taintResult.get(pointer);
    }

    private void addSourceTaint() {
        for (Invoke invoke : allInvokes) {
            if (invoke.getLValue() == null) continue;
            for (Source source : config.getSources()) {
                if (invoke.getMethodRef().resolve().equals(source.method())) {
                    csManager.getCSVarsOf(invoke.getLValue()).forEach(csVar ->
                            workList.addEntry(csVar, new PointsToSet(manager.makeTaint(invoke, source.type()))));
                    break;
                }
            }
        }
    }

    private void checkTaints(Set<TaintFlow> taintFlows) {
        for (Invoke invoke : allInvokes) {
            for (Sink sink : config.getSinks()) {
                if (invoke.getMethodRef().resolve().equals(sink.method())) {
                    for (CSVar csVar : csManager.getCSVarsOf(invoke.getInvokeExp().getArg(sink.index()))) {
                        if (taintResult.containsKey(csVar)) {
                            taintResult.get(csVar).forEach(o ->
                                    taintFlows.add(new TaintFlow(manager.getSourceCall(o), invoke, sink.index())));
                        }
                    }
                }
            }
        }
    }

    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry e = workList.pollEntry();
            PointsToSet diff = propagate(e.pointer(), e.pointsToSet());
            if (!diff.isEmpty()) {
                propagateTaints(e.pointer(), diff);
            }
        }
    }

    private void propagateTaints(Pointer pointer, PointsToSet pointsToSet) {
        if (!(pointer instanceof CSVar csVar)) return;
        for (Invoke invoke : allInvokes) {
            for (TaintTransfer transfer : config.getTransfers()) {
                if (invoke.getMethodRef().resolve().equals(transfer.method())) {
                    if (transfer.from() == TaintTransfer.BASE && csVar.getVar().equals(((InvokeInstanceExp)invoke.getInvokeExp()).getBase())) {
                        PointsToSet pts = new PointsToSet();
                        for (Obj obj : pointsToSet) {
                            pts.addObject(manager.makeTaint(manager.getSourceCall(obj), transfer.type()));
                        }
                        workList.addEntry(csManager.getCSVar(csVar.getContext(), invoke.getLValue()), pts);
                        break;
                    }
                    else if (transfer.from() >= 0 && csVar.getVar().equals(invoke.getInvokeExp().getArg(transfer.from()))) {
                        PointsToSet pts = new PointsToSet();
                        if (transfer.to() == TaintTransfer.BASE) {
                            for (Obj obj : pointsToSet) {
                                pts.addObject(manager.makeTaint(manager.getSourceCall(obj), transfer.type()));
                            }
                            workList.addEntry(csManager.getCSVar(csVar.getContext(), ((InvokeInstanceExp)invoke.getInvokeExp()).getBase()), pts);
                        }
                        else {
                            for (Obj obj : pointsToSet) {
                                pts.addObject(manager.makeTaint(manager.getSourceCall(obj), transfer.type()));
                            }
                            workList.addEntry(csManager.getCSVar(csVar.getContext(), invoke.getLValue()), pts);
                        }
                        break;
                    }
                }
            }
        }
    }

    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diff = new PointsToSet();
        pointsToSet.objects().filter(o -> !getTaintPtsOfPointer(pointer).contains(o)).forEach(diff::addObject);

        if (!diff.isEmpty()) {
            diff.objects().forEach(getTaintPtsOfPointer(pointer)::addObject);
            solver.getSuccsOf(pointer).forEach(t -> workList.addEntry(t, diff));
        }
        return diff;
    }

}

class WorkList {

    private final Queue<Entry> entries = new ArrayDeque<>();

    /**
     * Adds an entry to the work list.
     */
    void addEntry(Pointer pointer, PointsToSet pointsToSet) {
        entries.add(new Entry(pointer, pointsToSet));
    }

    /**
     * Retrieves and removes an entry from this queue, or returns null
     * if this work list is empty.
     */
    Entry pollEntry() {
        return entries.poll();
    }

    /**
     * @return true if the work list is empty, otherwise false.
     */
    boolean isEmpty() {
        return entries.isEmpty();
    }

    /**
     * Represents entries in the work list.
     * Each entry consists of a pointer and a points-to set.
     */
    record Entry(Pointer pointer, PointsToSet pointsToSet) {
    }
}

class PointsToSet implements Iterable<Obj> {

    private final Set<Obj> set = Sets.newHybridSet();

    /**
     * Constructs an empty points-to set.
     */
    PointsToSet() {
    }

    /**
     * Constructs a points-to set containing one object.
     */
    PointsToSet(Obj obj) {
        addObject(obj);
    }

    /**
     * Adds an object to this set.
     *
     * @return true if this points-to set changed as a result of the call,
     * otherwise false.
     */
    boolean addObject(Obj obj) {
        return set.add(obj);
    }

    /**
     * @return true if this points-to set contains the given object, otherwise false.
     */
    boolean contains(Obj obj) {
        return set.contains(obj);
    }

    /**
     * @return whether this set if empty.
     */
    boolean isEmpty() {
        return set.isEmpty();
    }

    /**
     * @return the number of objects in this set.
     */
    int size() {
        return set.size();
    }

    /**
     * @return all objects in this set.
     */
    Stream<Obj> objects() {
        return set.stream();
    }

    /**
     * @return all objects in this set.
     */
    Set<Obj> getObjects() {
        return Collections.unmodifiableSet(set);
    }

    @Override
    public Iterator<Obj> iterator() {
        return set.iterator();
    }

    @Override
    public String toString() {
        return set.toString();
    }
}