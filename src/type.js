// Type Inference
// Based on http://dev.stephendiehl.com/fun/006_hindley_milner.html
const { sum } = require("styp");
const { equal } = require("saman");
const { Expr } = require("./ast");

// Type Defs
const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TArr: ["t1", "t2"]
});

const Scheme = sum("Scheme", {
    Forall: ["var", "type"]
});

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");
const TUnit = Type.TCon("unit");

const PrimTypes = {
    "int":TInt,
    "bool":TBool,
    "unit":TUnit
};

const optypes = {
    "ADD": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "MUL": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "SUB": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "DIV": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "AND": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "OR": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "GT": Type.TArr(TInt,Type.TArr(TInt,TBool)),
    "LT": Type.TArr(TInt,Type.TArr(TInt,TBool)),
    "NOT": Type.TArr(TBool,TBool),
    "NEG": Type.TArr(TInt,TInt),
    "EQ": Scheme.Forall(
        [Type.TVar("o1"),Type.TVar("o2")],
        Type.TArr(Type.TVar("o1"),Type.TArr(Type.TVar("o2"),TBool))
    )
}

function printType(type,level=0) {
    return Type.is(type) ?
        type.cata({
            TCon: ({ name }) => name,
            TVar: ({ v }) => v,
            TArr: ({ t1, t2 }) => {
                return `${level%3?"(":""}${printType(t1,level+1)} -> ${printType(t2,level+1)}${level%3?")":""}`;
            }
        }):
        Scheme.is(type) && type.var.length ?
        `forall ${type.var.map(e => printType(e)).join(" ")}. ${printType(type.type)}`:
        printType(type.type)
}

// const Constraint = tagged("ConstraintEq",["left","right"]);

// Error
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable: '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable: '${name}'`);
const notUnifiable = (type1, type2, msg = "") => genericError(`Cannot unify types: ${printType(type1)} with ${printType(type2)} ${msg}`);
const failedOccursCheck = (v,name) => genericError(`Cannot construct infinite type: ${printType(v)} = ${printType(name)}`);

class TypeEnv {
    constructor(parent) {
        this.env = {};
        this.parent = parent;
    }

    exists(name) {
        if (this.env[name]) return this.env[name];
        else if (this.parent) return this.parent.lookUp(name);
        return false;
    }

    addBinding(name, type) {
        this.env[name] = type
    }

    removeBinding(name) {
        delete this.env[name]
    }

    lookUp(name) {  
        if (this.env[name]) return this.env[name];
        if (this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

// Will convert from on-line solver to 
// Equation based Constraint Solving/Unification later
class TypeVerifier {
    constructor() {
        this.env = new TypeEnv(null);
        this.subst = {};
        this.varInit();
        // this.constraints = [];
    }

    varInit() {
        this.names = {};
        this.count = 0;
        for(let i = "a".charCodeAt(0);i < "z".charCodeAt(0);i++) {
            this.names[i-97] = [String.fromCharCode(i),0];
        }
    }

    fresh() {
        const pair = this.names[this.count++ % 25];
        let n = pair[1]++;
        return Type.TVar(`${pair[0]}${n?n:""}`);
    }

    lookUp(name,env) {
        const t = env.lookUp(name);
        return Scheme.Forall.is(t) ? this.instantiate(t) : t;
    }

    // addConstraint(type1,type2) {
    //     this.constraints.push(Constraint(type1,type2));
    // }

    occursCheck(v, t, subst) {
        if (equal(v, t)) return true;
        if (Type.TVar.is(t) && t.v in subst)
            return this.occursCheck(v, subst[t.v], subst);
        if (Type.TArr.is(t))
            return this.occursCheck(v, t.t1, subst) || this.occursCheck(v, t.t2, subst);
        return false;
    }

    unifyVar(v, t, subst) {
        if (v.v in subst) return this.unify(subst[v.v], t, subst);
        if (Type.TVar.is(t) && t.v in subst) return this.unify(v, subst[t.v], subst);
        if (this.occursCheck(v, t, subst)) failedOccursCheck(v,t);
        else {
            subst[v.v] = t;
            return subst;
        }
    }

    unify(t1, t2, subst = this.subst) {
        if (equal(t1, t2)) return subst;
        if (Type.TVar.is(t1)) return this.unifyVar(t1, t2, subst);
        if (Type.TVar.is(t2)) return this.unifyVar(t2, t1, subst);
        if (Type.TArr.is(t1) && Type.TArr.is(t2)) {
            subst = this.unify(t1.t1, t2.t1, subst);
            return this.unify(t1.t2, t2.t2, subst);
        }
        notUnifiable(t1, t2);
    }

    apply(typ, subst = this.subst) {
        if (!subst) return null;
        if (Object.keys(subst).length == 0) return typ;
        if (equal(typ, TInt) || equal(typ, TBool)) return typ;
        if (Type.TVar.is(typ))
            return typ.v in subst? this.apply(subst[typ.v], subst):typ;
        if (Type.TArr.is(typ))
            return Type.TArr(
                this.apply(typ.t1, subst),
                this.apply(typ.t2, subst)
            );
        if (Scheme.Forall.is(typ)) {
            typ.var.forEach(v => delete subst[v.v]);
            return Scheme.Forall(typ.var, this.apply(typ.type, subst));
        }
        return null;
    }

    applyEnv(env, subst=this.subst) {
        for(let t in env.env) {
            env.env[t] = this.apply(env.env[t],subst);
        }
        if(env.parent) this.applyEnv(env.parent,subst);
        return env;
    }

    ftv(type) {
        if(Type.is(type)) return type.cata({
            TCon: c => new Set(),
            TVar: ({ v }) => new Set([v]),
            TArr: ({ t1, t2 }) => new Set([...this.ftv(t1), ...this.ftv(t2)])
        });
        if (Scheme.is(type)) {
            const bounded = new Set(type.var.map(v => v.v));
            return new Set([...(this.ftv(type.type))].filter(v => !bounded.has(v)));
        }
        return null;
    }

    ftvEnv(env) {
        const curr = Object.values(env.env).map(t => Array.from(this.ftv(t)));
        if(env.parent) curr.push([...(this.ftvEnv(env.parent))]);
        return new Set(curr.flat());
    }

    instantiate(type) {
        const ns = {}
        type.var.map(v => ns[v.v] = this.fresh());
        return this.apply(type.type, ns);
    }

    generalize(type, env) {
        const enftv = this.ftvEnv(env);
        const as = new Set([...(this.ftv(type))].filter(v => !enftv.has(v)));
        return Scheme.Forall([...as].map(v => Type.TVar(v)), type);
    }

    inferLet(ast,env) {
        if (env.exists(ast.name)) defInScope(ast.name);
        const t1 = this.infer(ast.e1,env);
        const tdash = this.generalize(t1,this.applyEnv(env,this.subst));
        if(ast.e2) {
            const ne = new TypeEnv(env);
            ne.addBinding(ast.name, tdash);
            return this.infer(ast.e2,ne);
        }
        env.addBinding(ast.name,tdash);
        return tdash;
    }

    inferCond(ast,env) {
        const cond = this.infer(ast.cond, env);
        const t1 = this.infer(ast.e1, env);
        const t2 = this.infer(ast.e2, env);
        this.unify(cond, TBool);
        this.unify(t1, t2);
        return this.apply(t1);
    }

    inferLam(ast,env) {
        const tv = this.fresh();
        const ne = new TypeEnv(env);
        ne.addBinding(ast.param, Scheme.Forall([],tv));
        const body = this.infer(ast.body, ne);
        return this.apply(Type.TArr(tv, body));
    }

    inferApp(ast,env) {
        const t1 = this.infer(ast.e1, env);
        const t2 = this.infer(ast.e2, this.applyEnv(env));
        const tv = this.fresh();
        this.unify(this.apply(t1), Type.TArr(t2, tv));
        return this.apply(tv);
    }

    inferFix(ast,env) {
        const t = this.infer(ast.e,env);
        const tv = this.fresh();
        this.unify(Type.TArr(tv,tv),t);
        return this.apply(tv);
    }  

    inferUnOp(ast,env) {
        const t = this.infer(ast.v,env);
        const tv = this.fresh();
        this.unify(Type.TArr(t,tv),optypes[ast.op]);
        return this.apply(tv);
    }
    
    inferBinOp(ast,env) {
        const t1 = this.infer(ast.l,env);
        const t2 = this.infer(ast.r,env);
        const tv = this.fresh();
        let op = optypes[ast.op];
        if(Scheme.Forall.is(op)) op = this.instantiate(op);
        this.unify(Type.TArr(t1,Type.TArr(t2,tv)),op);
        return this.apply(tv);
    }

    inferPair(ast,env) {
        const fst = this.infer(ast.fst,env);
        const snd = this.infer(ast.snd,env);
        const tv = this.fresh();
        return Type.TArr(Type.TArr(fst,Type.TArr(snd,tv)),tv);
    }

    infer(ast, env = this.env) {
        return ast.cata({
            Lit: ({ type }) =>  PrimTypes[type],
            Var: ({ name }) => this.lookUp(name,env),
            Pair: p => this.inferPair(p,env),
            UnOp: u => this.inferUnOp(u,env),
            BinOp: b => this.inferBinOp(b,env),
            Let: lb => this.inferLet(lb,env),
            Cond: c => this.inferCond(c,env),
            Lam: l => this.inferLam(l,env),
            App: a => this.inferApp(a,env),
            Fix: f => this.inferFix(f,env)
        });
    }

    alphaOrder(t) {
        let i = 0;
        const ns = {}
        const as = t.var[0] && t.var[0].v == "a" ? 
                   t.var : 
                   t.var
                    .map(v => ns[v.v] = Type.TVar(String.fromCharCode((i++)+97)));
        return Scheme.Forall(as, this.apply(t.type, ns));
    }

    getType(name) {
        const t = this.env.lookUp(name);
        if(Scheme.Forall.is(t)) return printType(this.alphaOrder(t));
        return printType(t);
    }

    getTypeEnv() {
        return Object.keys(this.env.env).map(k => `${k} :: ${this.getType(k)}`)
    }

    is(ast) {
        this.subst = {};
        return printType(this.infer(ast));
    }
}

module.exports = TypeVerifier;