// Evaluater
const { Expr } = require("./ast");
const Parser = require("./parser");
const TypeVerifier = require("./type");
const Prelude = require("./prelude");

// Eval types
const need = 0;
const name = 1;
const value = 2;

// const uops = ["NEG", "NOT"];
// const bops = ["ADD", "SUB", "DIV", "MUL", "AND", "OR", "GT", "LT", "EQ"];

class Env {
    constructor(params, args, outer = null, obj = null) {
        if (obj == null) {
            this.env = {};
            for (let i in args) {
                this.env[params[i]] = args[i];
            }
        } else {
            this.env = obj;
        }
        this.outer = outer;
    }

    find(variable) {
        if (variable in this.env) {
            return this.env[variable];
        } else if (this.outer) {
            return this.outer.find(variable);
        }
    }

    update(variable, value) {
        if (variable in this.env) {
            this.env[variable] = value;
            return this.env[variable];
        } else if (this.outer) {
            return this.outer.update(variable, value);
        }
    }

    create(variable, value) {
        return this.env[variable] = value;
    }
}

class Thunk {
    constructor(exp, env = null,intp) {
        this.exp = exp;
        this.scope = env;
        this.reduced = false;
        this.intp = intp;
    }

    value() {
        return this.intp.ieval(this.exp, this.scope);
    }

    reduce() {
        if(!this.reduced)
        {
            this.exp = this.intp.ieval(this.exp, this.scope);
            this.reduced = true;
        }
        return this.exp;
    }

    toString() {
        return `<thunk>`;   
    }
}

class Lambda {
    constructor(body, param, env = null, intp) {
        this.body = body;
        this.param = param;
        this.scope = env;
        this.intp = intp;
    }

    apply(actual) {
        let frame = new Env(null, null, this.scope, {});
        frame.create(this.param, actual);
        const out = this.intp.ieval(this.body, frame);
        return out;
    }

    toString() {
        return this.scope && this.scope != GLOBAL?"<closure>":"<lambda>";   
    }
}

function pair(fst,snd) {
    this.apply = function(f) {
        return f.apply(fst).apply(snd);
    }
}

pair.prototype.toString = function() {
    return `(${this[0]},${this[1]})`
}

const opfuns = {
    "ADD": (a,b) => a + b,
    "MUL": (a,b) => a * b,
    "SUB": (a,b) => a - b,
    "DIV": (a,b) => a / b,
    "AND": (a,b) => a && b,
    "OR": (a,b) => a || b,
    "GT": (a,b) => a > b,
    "LT": (a,b) => a < b,
    "EQ": (a,b) => a == b,
    "NOT": a => !a,
    "NEG": a => -a
}

function globalEnv() {
    const env = new Env();
    // Will add more
    // env.create("fst",{ apply: v => v[0] });
    // env.create("snd",{ apply: v => v[1] });
    // env.create("print",{ apply: v => console.log(v) });
    return env;
}

const GLOBAL = globalEnv();

class Interpreter { 
    constructor(global) {
        this.parser = new Parser();
        this.infer = new TypeVerifier();
        this.mode = value;
        this.global = global?global:GLOBAL;
        // Prelude.forEach(f => this.evaluate(f));
    }

    setMode(mode) {
        this.mode = mode;
    }

    ieval(ast, env) {
        if (Expr.Lit.is(ast)) return ast.val;
        if (Expr.Pair.is(ast)) return new pair(
            this.ieval(ast.fst,env),
            this.ieval(ast.snd,env)
        );
        if(Expr.Let.is(ast)) {
            const e1 = this.ieval(ast.exp,env);
            if(ast.e2) {
                let ls = new Env(null, null, env, {});
                ls.create(ast.name, e1);
                return this.ieval(ast.e2,ls);
            }
            return env.create(ast.name,e1);
        }
        if (Expr.Var.is(ast)) {
            const v = env.find(ast.name);
            if (v instanceof Thunk) {
                if(this.mode == name) return v.value();
                return v.reduce();
            }
            return v;
        }
        if (Expr.Cond.is(ast)) {
            const cond = this.ieval(ast.cond, env);
            if (cond) return this.ieval(ast.e1, env);
            return this.ieval(ast.e2, env);
        }
        if (Expr.Lam.is(ast))
            return new Lambda(ast.body, ast.param, env, this);
        if (Expr.App.is(ast)) {
            const lam = this.ieval(ast.e1,env);
            if(this.mode == value) return lam.apply(this.ieval(ast.e2,env));
            return lam.apply(new Thunk(ast.e2,env,this));
        }
        if(Expr.Fix.is(ast))
            return Expr.App(ast,Expr.Fix(ast.e));
        if (Expr.BinOp.is(ast)) 
            return opfuns[ast.op](this.ieval(ast.l, env),this.ieval(ast.r, env));
        if (Expr.UnOp.is(ast)) return opfuns[ast.op](this.ieval(ast.val,env));
    }

    evaluate(str) {
        const ast = this.parser.parse(str);
        const type = this.infer.is(ast);
        const output = this.ieval(ast,this.global);
        return { output:output, type:type };
    }
}

module.exports =  {
    Interpreter:Interpreter, 
    modes: {
        "need":need,
        "name":name,
        "value":value
    }
};