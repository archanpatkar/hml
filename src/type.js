// Type checker
// Based on http://dev.stephendiehl.com/fun/006_hindley_milner.html
const { sum } = require("styp");
const { equal, merge } = require("saman");

const Type = sum("Types", {
    TVar:["v"],
    TCon:["name"],
    // TPair:["cons","cdr"],
    TArr:["t1","t2"]
});

const Scheme = sum("Scheme", {
    Forall:["var","type"]
});

// temp
const Lam = (param, type, body) => ({ node: "lambda", param: param, type: type, body: body });
const Pair = (fst,snd) => ({ node:"pair", fst:fst, snd:snd });
const Lit = (type, val) => ({ node: "literal", type: type, val: val });
const Var = (name) => ({ node: "var", name: name });
const LetB = (name,exp) => ({ node: "let", name: name, exp:exp });
const App = (lam, param) => ({ node: "apply", exp1: lam, exp2: param });
const Condition = (cond,e1,e2) => ({ node: "condition", cond:cond, exp1: e1, exp2: e2 });
const BinOp = (op, l, r) => ({ node: op, l: l, r: r });
const UnOp = (op,v) => ({ node: op, val: v });

// Work in progress
const Expr = sum("Expr", {
    Var:["name"],
    App:["e1","e2"],
    Lit:["type","val"],
    Lam:["param","body"],
    Cond:["cond","e1","e2"]
});

// const Constraint = tagged("ConstraintEq",["left","right"]);

// const TypeEnv = () => new Map();

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");

const ops = ["ADD", "SUB", "DIV", "MUL"]
// const printType = (type) => Array.isArray(type) ? `(${printType(type[0])}->${printType(type[1])})` : type;

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable --> '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable --> '${name}'`);
const notUnifiable = (type1,type2,msg="") => genericError(`Cannot unify types: '${type1.toString()}' with '${type2.toString()}' ${msg}`);
const failedOccursCheck = (name) => genericError(`Failed Occurs Check --> '${name.toString()}'`);
// const notType = (type,msg) => genericError(`Expected type '${printType(type)}' ${msg}`);
// const typeMismatch = (type1,type2) => genericError(`Couldn't match the expected type: ${printType(type1)} with type: ${printType(type2)}`);
// const nonFunction = (type) => genericError(`Tried to apply to non-Function type --> ${type}`);

class TypeEnv {
    constructor(parent) {
        this.env = {};
        this.parent = parent;
    }

    exists(name) {
        if (this.env[name]) return this.env[name];
        else if(this.parent) return this.parent.lookUp(name);
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
        if(this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

class TypeChecker {
    constructor() {
        this.sym = new TypeEnv(null);
        this.count = 0;
        this.subst = {};
        // this.constraints = [];
        // this.variables = [];
        // this.ctable = new Map();
    }

    fresh() {
        let temp = "t" + this.count++;
        // this.variables.push(temp);
        return Type.TVar(temp);
    }

    // addConstraint(type1,type2) {
    //     this.ctable.set(type1,type2);
    //     this.constraints.push(Constraint(type1,type2));
    // }

    occursCheck(v,t,subst) {
        if(equal(v,t)) return true;
        if(Type.TVar.is(t) && t.v in subst) 
            return this.occursCheck(v,subst[t.v],subst);
        if(Type.TArr.is(t))
            return this.occursCheck(v,t.t1,subst) || this.occursCheck(v,t.t2,subst);
        return false;
    }

    unifyVar(v,t,subst) {
        if(v.v in subst) return this.unify(subst[v.v],t,subst);
        if(Type.TVar.is(t) && t.v in subst) return this.unify(v,subst[t.v],subst);
        if(this.occursCheck(v,t,subst)) failedOccursCheck(v);
        else {
            subst[v.v] = t;
            return subst;
        }
    }

    unify(t1,t2,subst={}) {
        if(equal(t1,t2)) return subst;
        if(Type.TVar.is(t1)) return this.unifyVar(t1,t2,subst);
        if(Type.TVar.is(t2)) return this.unifyVar(t2,t1,subst);
        if(Type.TArr.is(t1) && Type.TArr.is(t2)) {
            subst = this.unify(t1.t1,t2.t1,subst);
            return this.unify(t1.t2,t2.t2,subst);
        }
        notUnifiable(t1,t2);
    }

    apply(typ,subst=this.subst) {
        if(!subst) return null;
        if(Object.keys(subst).length == 0) return typ;
        if(equal(typ,TInt) || equal(typ,TBool)) return typ;
        if(Type.TVar.is(typ)) {
            if(typ.v in subst) return this.apply(subst[typ.v],subst);
            return typ;
        }
        if(Type.TArr.is(typ)) {
            return Type.TArr(
                this.apply(typ.t1,subst),
                this.apply(typ.t2,subst)
            );
        }
        if(Scheme.Forall.is(typ)) {
            typ.var.forEach(v => delete subst[v.v]);
            return Scheme.Forall(type.var,this.apply(typ.type,subst));
        }
        return null;
    }

    ftv(type) {
        if(Type.TCon.is(type)) return new Set();
        if(Type.TVar.is(type)) return new Set([type.v]);
        if(Type.TArr.is(type)) return new Set([...this.ftv(type.t1),...this.ftv(type.t2)]);
        if(Scheme.Forall.is(type)) {
            const bounded = new Set(type.var.map(v => v.v));
            return new Set([...this.ftv(type.type)].filter(v => !bounded.has(v)));
        }
        return null;
    }

    instantiate(type) {
        // let t1,t2;
        // if(Type.TVar.is(type.t1)) t1 = this.fresh();
        // if(Type.TArr.is(type.t2)) t2 = this.instantiate(type.t2);
        // else if(Type.TVar.is(type.t2)) t2 = this.fresh();
        // else t2 = type.t2;
        // return Type.TArr(t1,t2);
    }

    generalize(type) {
        
    }

    infer(ast,sym=this.sym) {
        if (ast.node == "literal") 
            return ast.type == "int"? TInt:TBool;
        else if (ast.node == "var") {
            const t = sym.lookUp(ast.name);
            // this.instantiate(t);
            return t;
        }
        else if (ast.node == "let") {
            if(sym.exists(ast.name)) defInScope(ast.name);
            // this.generalize(t);
            return null;
        }
        else if (ast.node == "condition") {
            const cond = this.infer(ast.cond,sym);
            const t1 = this.infer(ast.exp1,sym);
            const t2 = this.infer(ast.exp2,sym);
            const u1 = this.unify(cond,TBool);
            const u2 = this.unify(t1,t2);
            this.subst = merge(this.subst,merge(u1,u2));
            return this.apply(t1);
        }
        else if (ast.node == "lambda") {
            const ne = new TypeEnv(sym);
            const tv = this.fresh();
            ne.addBinding(ast.param, tv);
            const body = this.infer(ast.body,ne);
            return this.apply(Type.TArr(tv,body));
        }
        else if (ast.node == "apply") {
            const tv = this.fresh();
            const t1 = this.infer(ast.exp1,sym);
            const t2 = this.infer(ast.exp2,sym);
            this.subst = merge(this.subst,this.unify(this.apply(t1),Type.TArr(t2,tv)));
            return this.apply(tv);
        }
        return;
    }

    prove(ast) {
        // printType()
        return this.infer(ast).toString();
    }
}



const tc1 = new TypeChecker();
let code = App(
    Lam("x",null,
        Condition(
            Lit("bool",true),
            Var("x"),
            Lit("int",0)
        )
    ),
    Lit("int",10)
);
let code2 = Lam("x",null,
Condition(
    Lit("bool",true),
    Var("x"),
    Lit("int",0)
));
let code3 = Lam("x",null,
Condition(
    Var("x"),
    Lit("int",10),
    Lit("int",0)
));



console.log(tc1.prove(code));


module.exports = TypeChecker;