use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use crate::ast;
use crate::env::Env;
use crate::interpreter::{InterpretError, InterpretResult, Interpreter};
use crate::value::{InstanceValue, Value};

pub trait Callable: fmt::Debug {
    fn arity(&self) -> usize;
    fn call(&self, interpreter: &mut Interpreter, args: &[Value]) -> InterpretResult<Value>;
}

#[derive(Debug, Clone)]
pub struct FunctionCallable {
    fun: ast::FunDeclStmt,
    env: Rc<RefCell<Env>>,
    is_initializer: bool,
}

impl FunctionCallable {
    pub fn new(fun: ast::FunDeclStmt, env: Rc<RefCell<Env>>, is_initializer: bool) -> Self {
        Self {
            fun,
            env,
            is_initializer,
        }
    }

    pub fn bind(&self, instance: Rc<RefCell<InstanceValue>>) -> Self {
        let mut bound_env = Env::with_parent(Rc::clone(&self.env));
        bound_env.define("this".to_string(), Value::Instance(instance));

        Self::new(
            self.fun.clone(),
            Rc::new(RefCell::new(bound_env)),
            self.is_initializer,
        )
    }
}

impl Callable for FunctionCallable {
    fn arity(&self) -> usize {
        self.fun.params().len()
    }

    fn call(&self, interpreter: &mut Interpreter, args: &[Value]) -> InterpretResult<Value> {
        assert_eq!(
            self.fun.params().len(),
            args.len(),
            "Exact number of args must be provided",
        );

        let mut new_env = Env::with_parent(Rc::clone(&self.env));
        for (param, arg) in self.fun.params().iter().zip(args.iter()) {
            new_env.define(param.to_string(), arg.clone());
        }

        let old_env = interpreter.replace_env(Rc::new(RefCell::new(new_env)));

        let res = interpreter.interpret_stmts(self.fun.body());

        interpreter.set_env(old_env);

        let produced_res = match res {
            // No return statement encountered
            Ok(()) => Ok(Value::Nil),
            // Return statement triggered the special `Return` error
            Err(InterpretError::Return(value)) => Ok(value),
            // Other error
            Err(err) => Err(err),
        };

        produced_res.map(|value| {
            if self.is_initializer {
                self.env.borrow().get_at_distance("this", 0)
            } else {
                value
            }
        })
    }
}

impl PartialEq for FunctionCallable {
    fn eq(&self, other: &Self) -> bool {
        self.fun == other.fun && Rc::ptr_eq(&self.env, &other.env)
    }
}

#[derive(Debug)]
pub struct NativeCallableClock;

impl Callable for NativeCallableClock {
    fn arity(&self) -> usize {
        0
    }

    fn call(&self, _: &mut Interpreter, _: &[Value]) -> InterpretResult<Value> {
        let now = SystemTime::now();
        let since_the_epoch = now
            .duration_since(UNIX_EPOCH)
            .unwrap_or(Duration::from_secs(0));
        let secs = since_the_epoch.as_millis() as f64 / 1000.0;

        Ok(Value::Number(secs))
    }
}
