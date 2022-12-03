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
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private Map<Var, Set<Var>> aliasVars;
    private Map<JField, Set<LoadField>> staticLoadFields;
    private Map<JField, Set<StoreField>> staticStoreFields;


    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        aliasVars = new HashMap<>();
        for (Var a : pta.getVars()) {
            Set<Var> set = new HashSet<>();
            for (Var b : pta.getVars()) {
                if (pta.getPointsToSet(a).stream().anyMatch(o -> pta.getPointsToSet(b).contains(o))) {
                    set.add(b);
                }
            }
            aliasVars.put(a, set);
        }
        staticLoadFields = new HashMap<>();
        staticStoreFields = new HashMap<>();

        icfg.forEach(stmt -> {
            if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                JField field = storeField.getFieldRef().resolve();
                if (staticStoreFields.containsKey(field)){
                    staticStoreFields.get(field).add(storeField);
                }
                else {
                    Set<StoreField> set = new HashSet<>();
                    set.add(storeField);
                    staticStoreFields.put(field, set);
                }
            }
            else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                JField field = loadField.getFieldRef().resolve();
                if (staticLoadFields.containsKey(field)){
                    staticLoadFields.get(field).add(loadField);
                }
                else {
                    Set<LoadField> set = new HashSet<>();
                    set.add(loadField);
                    staticLoadFields.put(field, set);
                }
            }
        });
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
        return out.copyFrom(in);
    }

    private boolean testIndex(Value i, Value j) {
        if (i.isUndef() || j.isUndef()) return false;
        if (i.isNAC() || j.isNAC()) return true;
        return i.getConstant() == j.getConstant();
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof StoreField storeField && ConstantPropagation.canHoldInt(storeField.getRValue())) {
            if (storeField.isStatic()) {
                JField field = storeField.getFieldRef().resolve();
                if (staticLoadFields.containsKey(field)){
                    staticLoadFields.get(field).forEach(solver::addNode);
                }
            }
            else {
                Var base = ((InstanceFieldAccess)storeField.getFieldAccess()).getBase();
                if (aliasVars.containsKey(base)) {
                    for (Var alias : aliasVars.get(base)) {
                        alias.getLoadFields().forEach(solver::addNode);
                    }
                }
            }
        }
        else if (stmt instanceof LoadField loadField && ConstantPropagation.canHoldInt(loadField.getLValue())) {
            CPFact ic = in.copy();
            Value val = Value.getUndef();
            if (loadField.isStatic()) {
                if (staticStoreFields.containsKey(loadField.getFieldRef().resolve())) {
                    for (StoreField storeField : staticStoreFields.get(loadField.getFieldRef().resolve())) {
                        val = cp.meetValue(val, solver.getInFact(storeField).get(storeField.getRValue()));
                    }
                }
            }
            else {
                Var base = ((InstanceFieldAccess)loadField.getFieldAccess()).getBase();
                if (aliasVars.containsKey(base)) {
                    for (Var alias : aliasVars.get(base)) {
                        for (StoreField storeField : alias.getStoreFields()) {
                            if (loadField.getFieldRef().resolve().equals(storeField.getFieldRef().resolve())) {
                                val = cp.meetValue(val, solver.getInFact(storeField).get(storeField.getRValue()));
                            }
                        }
                    }
                }
            }
            ic.update(loadField.getLValue(), val);
            return out.copyFrom(ic);
        }
        else if(stmt instanceof StoreArray storeArray && ConstantPropagation.canHoldInt(storeArray.getRValue())) {
            Var base = storeArray.getArrayAccess().getBase();
            if (aliasVars.containsKey(base)) {
                for (Var alias : aliasVars.get(base)) {
                    alias.getLoadArrays().forEach(solver::addNode);
                }
            }
        }
        else if (stmt instanceof LoadArray loadArray && ConstantPropagation.canHoldInt(loadArray.getLValue())) {
            CPFact ic = in.copy();
            Value val = Value.getUndef();
            Var base = loadArray.getArrayAccess().getBase();
            if (aliasVars.containsKey(base)) {
                for (Var alias : aliasVars.get(base)) {
                    for (StoreArray storeArray : alias.getStoreArrays()) {
                        if (testIndex(in.get(loadArray.getArrayAccess().getIndex()), solver.getInFact(storeArray).get(storeArray.getArrayAccess().getIndex()))) {
                            val = cp.meetValue(val, solver.getInFact(storeArray).get(storeArray.getRValue()));
                        }
                    }
                }
            }
            ic.update(loadArray.getLValue(), val);
            return out.copyFrom(ic);
        }

        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        Invoke invoke = (Invoke)edge.getSource();

        if (invoke.getLValue() == null) return out;

        CPFact oc = out.copy();
        oc.update(invoke.getLValue(), Value.getUndef());
        return oc;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        Invoke invoke = (Invoke)edge.getSource();
        InvokeExp invokeExp = invoke.getInvokeExp();
        JMethod callee = edge.getCallee();
        CPFact result = new CPFact();

        for (int i = 0; i < callee.getParamCount(); ++i) {
            IR calleeIR = icfg.getContainingMethodOf(edge.getTarget()).getIR();
            if (ConstantPropagation.canHoldInt(calleeIR.getParam(i))) {
                result.update(calleeIR.getParam(i), callSiteOut.get(invokeExp.getArg(i)));
            }
        }

        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        Invoke invoke = (Invoke)edge.getCallSite();
        CPFact result = new CPFact();

        if (invoke.getLValue() == null || !ConstantPropagation.canHoldInt(invoke.getLValue())) return result;

        IR calleeIR = icfg.getContainingMethodOf(edge.getSource()).getIR();
        for (Var v : calleeIR.getReturnVars()) {
            result.update(invoke.getResult(), cp.meetValue(result.get(invoke.getResult()), returnOut.get(v)));
        }
        return result;
    }
}
