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

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
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
        CPFact ret = new CPFact();
        for (Var p : cfg.getIR().getParams()){
            if (canHoldInt(p)){
                ret.update(p, Value.getNAC());
            }
        }
        return ret;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()){
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isUndef())
            return v2;
        if (v2.isUndef())
            return v1;
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();

        if (v1.equals(v2))
            return v1;
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        DefinitionStmt<?, ?> defstmt = null;
        Var defvar = null;
        if ((stmt instanceof DefinitionStmt<?,?>)){
            defstmt = (DefinitionStmt<?, ?>)stmt;
            if (defstmt.getLValue() instanceof Var){
                defvar = (Var)defstmt.getLValue();
                if (!canHoldInt(defvar))
                    return out.copyFrom(in);
            }
            else
                return out.copyFrom(in);
        }
        else
            return out.copyFrom(in);

        Value value = evaluate(defstmt.getRValue(), in);
        CPFact ic = in.copy();
        ic.update(defvar, value);
        return out.copyFrom(ic);
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
        Value ret = null;

        if (exp instanceof Var){
            ret = in. get((Var)exp);
        } else if (exp instanceof IntLiteral){
            ret = Value.makeConstant(((IntLiteral)exp).getValue());
        } else if (exp instanceof BinaryExp){
            BinaryExp bexp = (BinaryExp)exp;
            Value value1 = in.get(bexp.getOperand1());
            Value value2 = in.get(bexp.getOperand2());
            if (bexp instanceof ArithmeticExp){
                ArithmeticExp aexp = (ArithmeticExp)bexp;
                if ((aexp.getOperator() == ArithmeticExp.Op.DIV || aexp.getOperator() == ArithmeticExp.Op.REM) &&
                        value2.isConstant() &&
                        value2.getConstant() == 0) {
                    ret = Value.getUndef();
                } else if (value1.isNAC() || value2.isNAC()){
                    ret = Value.getNAC();
                } else if (value1.isUndef() || value2.isUndef()) {
                    ret = Value.getUndef();
                } else {
                    int c1 = value1.getConstant();
                    int c2 = value2.getConstant();
                    ret = switch (aexp.getOperator()) {
                        case ADD -> Value.makeConstant(c1 + c2);
                        case SUB -> Value.makeConstant(c1 - c2);
                        case MUL -> Value.makeConstant(c1 * c2);
                        case DIV -> Value.makeConstant(c1 / c2);
                        case REM -> Value.makeConstant(c1 % c2);
                    };
                }
            } else if (bexp instanceof ConditionExp) {
                ConditionExp cexp = (ConditionExp)bexp;
                if (value1.isNAC() || value2.isNAC()) {
                    ret = Value.getNAC();
                } else if (value1.isUndef() || value2.isUndef()) {
                    ret = Value.getUndef();
                } else {
                    int c1 = value1.getConstant();
                    int c2 = value2.getConstant();
                    ret = switch (cexp.getOperator()) {
                        case EQ -> Value.makeConstant((c1 == c2)? 1 : 0);
                        case GE -> Value.makeConstant((c1 >= c2)? 1 : 0);
                        case GT -> Value.makeConstant((c1 > c2)? 1 : 0);
                        case LE -> Value.makeConstant((c1 <= c2)? 1 : 0);
                        case LT -> Value.makeConstant((c1 < c2)? 1 : 0);
                        case NE -> Value.makeConstant((c1 != c2)? 1 : 0);
                    };
                }
            } else if (bexp instanceof ShiftExp) {
                ShiftExp sexp = (ShiftExp)bexp;
                if (value1.isNAC() || value2.isNAC()) {
                    ret = Value.getNAC();
                } else if (value1.isUndef() || value2.isUndef()) {
                    ret = Value.getUndef();
                } else {
                    int c1 = value1.getConstant();
                    int c2 = value2.getConstant();
                    ret = switch (sexp.getOperator()) {
                        case SHL -> Value.makeConstant(c1 << c2);
                        case SHR -> Value.makeConstant(c1 >> c2);
                        case USHR -> Value.makeConstant(c1 >>> c2);
                    };
                }
            } else if (bexp instanceof BitwiseExp) {
                BitwiseExp bwexp = (BitwiseExp) bexp;
                if (value1.isNAC() || value2.isNAC()) {
                    ret = Value.getNAC();
                } else if (value1.isUndef() || value2.isUndef()) {
                    ret = Value.getUndef();
                } else {
                    int c1 = value1.getConstant();
                    int c2 = value2.getConstant();
                    ret = switch (bwexp.getOperator()) {
                        case OR -> Value.makeConstant(c1 | c2);
                        case AND -> Value.makeConstant(c1 & c2);
                        case XOR -> Value.makeConstant(c1 ^ c2);
                    };
                }
            } else {
                ret = Value.getNAC();
            }
        } else {
            ret = Value.getNAC();
        }

        return ret;
    }
}
