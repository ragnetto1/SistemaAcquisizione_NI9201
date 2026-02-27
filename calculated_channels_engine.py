import ast
import re
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

import numpy as np

try:
    import scipy as sp  # type: ignore
except Exception:
    sp = None

try:
    import pandas as pd  # type: ignore
except Exception:
    pd = None


_CHANNEL_RE = re.compile(r"^(?:ai\d+|cc\d+|Fs)$")
_CC_RE = re.compile(r"^cc(\d+)$")

_DISALLOWED_NAME_CALLS = {
    "__import__",
    "eval",
    "exec",
    "open",
    "compile",
    "globals",
    "locals",
    "vars",
    "dir",
    "input",
    "getattr",
    "setattr",
    "delattr",
    "help",
}

_SAFE_BUILTINS: Dict[str, Callable[..., Any]] = {
    "abs": abs,
    "min": min,
    "max": max,
    "sum": sum,
    "len": len,
    "float": float,
    "int": int,
    "bool": bool,
    "round": round,
    "enumerate": enumerate,
    "range": range,
    "zip": zip,
    "__import__": __import__,
}


class FormulaValidationError(ValueError):
    pass


class _SafetyVisitor(ast.NodeVisitor):
    def __init__(self, allow_function_def: bool) -> None:
        super().__init__()
        self.allow_function_def = bool(allow_function_def)

    def _raise(self, msg: str) -> None:
        raise FormulaValidationError(msg)

    def visit_Import(self, node: ast.Import) -> None:
        self._raise("Import non consentito nelle formule.")

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        self._raise("Import non consentito nelle formule.")

    def visit_Global(self, node: ast.Global) -> None:
        self._raise("Uso di global non consentito.")

    def visit_Nonlocal(self, node: ast.Nonlocal) -> None:
        self._raise("Uso di nonlocal non consentito.")

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._raise("Definizione class non consentita.")

    def visit_Lambda(self, node: ast.Lambda) -> None:
        self._raise("Lambda non consentita.")

    def visit_While(self, node: ast.While) -> None:
        self._raise("While non consentito nelle formule.")

    def visit_Try(self, node: ast.Try) -> None:
        self._raise("Try/except non consentito nelle formule.")

    def visit_With(self, node: ast.With) -> None:
        self._raise("With non consentito nelle formule.")

    def visit_Delete(self, node: ast.Delete) -> None:
        self._raise("Delete non consentito nelle formule.")

    def visit_Raise(self, node: ast.Raise) -> None:
        self._raise("Raise non consentito nelle formule.")

    def visit_Await(self, node: ast.Await) -> None:
        self._raise("Await non consentito nelle formule.")

    def visit_Yield(self, node: ast.Yield) -> None:
        self._raise("Yield non consentito nelle formule.")

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        if not self.allow_function_def:
            self._raise("Formula non valida: usa un'espressione o una singola funzione def ccX(...).")
        self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._raise("Funzioni async non consentite.")

    def visit_Attribute(self, node: ast.Attribute) -> None:
        if str(node.attr).startswith("__"):
            self._raise("Attributi speciali non consentiti.")
        self.generic_visit(node)

    def visit_Name(self, node: ast.Name) -> None:
        if str(node.id).startswith("__"):
            self._raise("Nomi speciali non consentiti.")
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        fn = node.func
        if isinstance(fn, ast.Name):
            if fn.id in _DISALLOWED_NAME_CALLS:
                self._raise(f"Funzione non consentita: {fn.id}")
        elif isinstance(fn, ast.Attribute):
            if str(fn.attr).startswith("__"):
                self._raise("Chiamata a attributo speciale non consentita.")
        self.generic_visit(node)


@dataclass
class _CompiledFormula:
    channel_id: str
    formula: str
    kind: str
    deps: Set[str]
    code: Any
    func: Optional[Callable[..., Any]]
    func_args: Tuple[str, ...]


class CalculatedChannelsEngine:
    def __init__(self, max_channels: int = 30) -> None:
        self.max_channels = max(1, int(max_channels))
        self._formula_by_cc: Dict[str, str] = {}
        self._compiled_by_cc: Dict[str, _CompiledFormula] = {}
        self._compile_errors: Dict[str, str] = {}
        self._eval_order: List[str] = []
        self._enabled_cc: Set[str] = set()
        self._enabled_explicit: bool = False
        self._state_by_cc: Dict[str, Dict[str, Any]] = {}
        self._runtime_eval_cc: Optional[str] = None
        self._runtime_eval_len: int = 1

    @staticmethod
    def _sort_key_cc(channel_id: str) -> Tuple[int, str]:
        m = _CC_RE.match(str(channel_id or ""))
        if not m:
            return (10**9, str(channel_id or ""))
        try:
            return (int(m.group(1)), channel_id)
        except Exception:
            return (10**9, str(channel_id or ""))

    @staticmethod
    def _sanitize_formula_text(formula: str) -> str:
        return str(formula or "").replace("\r\n", "\n").strip()

    def _state_for_current_cc(self) -> Dict[str, Any]:
        cc = str(self._runtime_eval_cc or "").strip()
        if not cc:
            raise RuntimeError("Helper disponibile solo durante evaluate().")
        state = self._state_by_cc.get(cc)
        if state is None:
            state = {}
            self._state_by_cc[cc] = state
        return state

    def _normalize_helper_input(self, value: Any) -> np.ndarray:
        return self._normalize_input(value, max(1, int(self._runtime_eval_len or 1)))

    def _helper_session_max(self, value: Any) -> np.ndarray:
        arr = self._normalize_helper_input(value)
        state = self._state_for_current_cc()
        prev = state.get("session_max_last", None)
        out = np.maximum.accumulate(arr)
        if prev is not None:
            out = np.maximum(out, float(prev))
        state["session_max_last"] = float(out[-1]) if out.size > 0 else float(prev or 0.0)
        return np.ascontiguousarray(out, dtype=np.float64)

    def _helper_session_min(self, value: Any) -> np.ndarray:
        arr = self._normalize_helper_input(value)
        state = self._state_for_current_cc()
        prev = state.get("session_min_last", None)
        out = np.minimum.accumulate(arr)
        if prev is not None:
            out = np.minimum(out, float(prev))
        state["session_min_last"] = float(out[-1]) if out.size > 0 else float(prev or 0.0)
        return np.ascontiguousarray(out, dtype=np.float64)

    def _helper_running_mean(self, value: Any) -> np.ndarray:
        arr = self._normalize_helper_input(value)
        state = self._state_for_current_cc()
        prev_sum = float(state.get("running_mean_sum", 0.0) or 0.0)
        prev_count = int(state.get("running_mean_count", 0) or 0)
        csum = np.cumsum(arr, dtype=np.float64)
        idx = np.arange(1, arr.size + 1, dtype=np.float64)
        out = (prev_sum + csum) / (prev_count + idx)
        state["running_mean_sum"] = prev_sum + float(csum[-1]) if csum.size > 0 else prev_sum
        state["running_mean_count"] = prev_count + int(arr.size)
        return np.ascontiguousarray(out, dtype=np.float64)

    def _helper_moving_mean(self, value: Any, window: Any = 50) -> np.ndarray:
        arr = self._normalize_helper_input(value)
        try:
            win = int(float(window))
        except Exception:
            win = 1
        win = max(1, win)
        state = self._state_for_current_cc()
        tails = state.setdefault("moving_mean_tails", {})
        tail = np.asarray(tails.get(win, np.array([], dtype=np.float64)), dtype=np.float64).reshape(-1)
        if win <= 1:
            tails[win] = np.array([], dtype=np.float64)
            return np.ascontiguousarray(arr, dtype=np.float64)

        if tail.size > (win - 1):
            tail = tail[-(win - 1):]
        hist = np.concatenate((tail, arr)).astype(np.float64, copy=False) if tail.size > 0 else np.asarray(arr, dtype=np.float64)
        cs = np.cumsum(np.concatenate((np.array([0.0], dtype=np.float64), hist)))
        idx = np.arange(hist.size)
        start = np.maximum(0, idx - win + 1)
        sums = cs[idx + 1] - cs[start]
        counts = idx - start + 1
        ma = sums / counts
        tails[win] = hist[-(win - 1):] if (win - 1) > 0 else np.array([], dtype=np.float64)
        return np.ascontiguousarray(ma[-arr.size:], dtype=np.float64)

    def _allowed_eval_globals(self) -> Dict[str, Any]:
        return {
            "__builtins__": dict(_SAFE_BUILTINS),
            "np": np,
            "sp": sp,
            "pd": pd,
            # Funzioni helper stateful per statistiche storiche.
            "max_storico": self._helper_session_max,
            "min_storico": self._helper_session_min,
            "media_corrente": self._helper_running_mean,
            "media_mobile": self._helper_moving_mean,
            # Alias inglesi per leggibilità.
            "session_max": self._helper_session_max,
            "session_min": self._helper_session_min,
            "running_mean": self._helper_running_mean,
            "moving_mean": self._helper_moving_mean,
        }

    @staticmethod
    def _extract_name_deps(tree: ast.AST) -> Set[str]:
        deps: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Name):
                nm = str(node.id)
                if _CHANNEL_RE.match(nm):
                    deps.add(nm)
        return deps

    def _compile_expression(self, channel_id: str, formula: str) -> _CompiledFormula:
        try:
            tree = ast.parse(formula, mode="eval")
        except SyntaxError as exc:
            raise FormulaValidationError(f"Errore sintassi: {exc}") from exc

        _SafetyVisitor(allow_function_def=False).visit(tree)
        deps = self._extract_name_deps(tree)
        try:
            code = compile(tree, f"<formula:{channel_id}>", "eval")
        except Exception as exc:
            raise FormulaValidationError(f"Errore compilazione: {exc}") from exc

        return _CompiledFormula(
            channel_id=channel_id,
            formula=formula,
            kind="expr",
            deps=deps,
            code=code,
            func=None,
            func_args=(),
        )

    def _compile_function(self, channel_id: str, formula: str) -> _CompiledFormula:
        try:
            tree = ast.parse(formula, mode="exec")
        except SyntaxError as exc:
            raise FormulaValidationError(f"Errore sintassi: {exc}") from exc

        _SafetyVisitor(allow_function_def=True).visit(tree)

        body = list(getattr(tree, "body", []) or [])
        funcs = [n for n in body if isinstance(n, ast.FunctionDef)]
        other_nodes = [n for n in body if not isinstance(n, ast.FunctionDef)]

        if len(funcs) != 1 or other_nodes:
            raise FormulaValidationError("La formula funzione deve contenere una sola def ccX(...).")

        fn = funcs[0]
        if fn.name != channel_id:
            raise FormulaValidationError(f"Nome funzione non valido: atteso '{channel_id}'.")
        if fn.decorator_list:
            raise FormulaValidationError("Decorator non consentiti.")

        args = fn.args
        if args.vararg is not None or args.kwarg is not None or args.kwonlyargs:
            raise FormulaValidationError("Usa solo argomenti espliciti (niente *args/**kwargs).")

        param_names = [str(a.arg) for a in list(args.args)]
        if len(set(param_names)) != len(param_names):
            raise FormulaValidationError("Argomenti funzione duplicati.")
        for p in param_names:
            if not _CHANNEL_RE.match(p):
                raise FormulaValidationError(f"Argomento non valido: {p}. Usa solo aiX, ccX o Fs.")

        used = self._extract_name_deps(tree)
        chan_refs = {x for x in used if x != "Fs"}
        missing_params = [x for x in sorted(chan_refs) if x not in param_names]
        if missing_params:
            raise FormulaValidationError(
                "Dipendenze non esplicite nei parametri funzione: " + ", ".join(missing_params)
            )

        deps = {x for x in param_names if _CHANNEL_RE.match(x)}

        try:
            code = compile(tree, f"<formula:{channel_id}>", "exec")
        except Exception as exc:
            raise FormulaValidationError(f"Errore compilazione: {exc}") from exc

        namespace = self._allowed_eval_globals()
        try:
            exec(code, namespace, namespace)
            fn_obj = namespace.get(channel_id)
        except Exception as exc:
            raise FormulaValidationError(f"Errore compilazione funzione: {exc}") from exc

        if not callable(fn_obj):
            raise FormulaValidationError("Funzione compilata non richiamabile.")

        return _CompiledFormula(
            channel_id=channel_id,
            formula=formula,
            kind="func",
            deps=deps,
            code=code,
            func=fn_obj,
            func_args=tuple(param_names),
        )

    def _compile_formula(self, channel_id: str, formula: str) -> _CompiledFormula:
        f = self._sanitize_formula_text(formula)
        if not f:
            raise FormulaValidationError("Formula vuota.")
        if f.startswith("def "):
            return self._compile_function(channel_id, f)
        return self._compile_expression(channel_id, f)

    @staticmethod
    def _toposort(nodes: Sequence[str], deps_map: Dict[str, Set[str]]) -> Tuple[List[str], Set[str]]:
        incoming: Dict[str, Set[str]] = {n: set() for n in nodes}
        outgoing: Dict[str, Set[str]] = {n: set() for n in nodes}
        for n in nodes:
            for d in deps_map.get(n, set()):
                if d not in incoming:
                    continue
                incoming[n].add(d)
                outgoing[d].add(n)

        ready = sorted([n for n in nodes if not incoming[n]], key=CalculatedChannelsEngine._sort_key_cc)
        order: List[str] = []
        while ready:
            cur = ready.pop(0)
            order.append(cur)
            for nxt in sorted(outgoing.get(cur, set()), key=CalculatedChannelsEngine._sort_key_cc):
                if cur in incoming.get(nxt, set()):
                    incoming[nxt].discard(cur)
                if not incoming[nxt] and nxt not in order and nxt not in ready:
                    ready.append(nxt)
            ready.sort(key=CalculatedChannelsEngine._sort_key_cc)

        cycle_nodes = {n for n in nodes if n not in order}
        return order, cycle_nodes

    def configure(self, formula_by_cc: Dict[str, str]) -> Dict[str, str]:
        cleaned: Dict[str, str] = {}
        for cc, formula in (formula_by_cc or {}).items():
            ccs = str(cc or "").strip()
            if not _CC_RE.match(ccs):
                continue
            if len(cleaned) >= self.max_channels:
                break
            cleaned[ccs] = self._sanitize_formula_text(formula)

        compile_errors: Dict[str, str] = {}
        compiled: Dict[str, _CompiledFormula] = {}

        for cc in sorted(cleaned.keys(), key=self._sort_key_cc):
            formula = cleaned.get(cc, "")
            if not formula:
                continue
            try:
                comp = self._compile_formula(cc, formula)
                compiled[cc] = comp
            except FormulaValidationError as exc:
                compile_errors[cc] = str(exc)
            except Exception as exc:
                compile_errors[cc] = f"Errore formula: {exc}"

        for cc, comp in list(compiled.items()):
            for dep in sorted(comp.deps):
                if dep.startswith("cc"):
                    dep_formula = cleaned.get(dep, "")
                    if not dep_formula:
                        compile_errors[cc] = f"Dipendenza non valida: {dep} senza formula."
                        break
            if cc in compile_errors:
                compiled.pop(cc, None)

        deps_map = {
            cc: {d for d in comp.deps if d.startswith("cc")}
            for cc, comp in compiled.items()
        }
        order, cycle_nodes = self._toposort(list(compiled.keys()), deps_map)
        if cycle_nodes:
            for cc in sorted(cycle_nodes, key=self._sort_key_cc):
                compile_errors[cc] = "Dipendenza circolare non ammessa."
                compiled.pop(cc, None)

        self._formula_by_cc = cleaned
        self._compiled_by_cc = compiled
        self._compile_errors = compile_errors
        self._eval_order = [cc for cc in order if cc in compiled]
        valid_cc = set(cleaned.keys())
        # Pulisce stato canali non piu presenti.
        for cc in list(self._state_by_cc.keys()):
            if cc not in valid_cc:
                self._state_by_cc.pop(cc, None)
        if not self._enabled_explicit:
            self._enabled_cc = set(valid_cc)
        else:
            old_enabled = set(self._enabled_cc)
            self._enabled_cc = {cc for cc in self._enabled_cc if cc in valid_cc}
            for cc in (old_enabled - self._enabled_cc):
                self._state_by_cc.pop(cc, None)
        return dict(self._compile_errors)

    def get_compile_errors(self) -> Dict[str, str]:
        return dict(self._compile_errors)

    def get_eval_order(self) -> List[str]:
        return list(self._eval_order)

    def set_enabled_channels(self, enabled_channel_ids: Sequence[str], reset_disabled: bool = True) -> None:
        new_enabled = {
            str(cc or "").strip()
            for cc in list(enabled_channel_ids or [])
            if _CC_RE.match(str(cc or "").strip())
        }
        if self._formula_by_cc:
            new_enabled = {cc for cc in new_enabled if cc in self._formula_by_cc}
        old_enabled = set(self._enabled_cc)
        self._enabled_cc = set(new_enabled)
        self._enabled_explicit = True

        # Sessione statistica: reset quando un canale viene disabilitato o ri-abilitato.
        if reset_disabled:
            for cc in (old_enabled - self._enabled_cc):
                self._state_by_cc.pop(cc, None)
        for cc in (self._enabled_cc - old_enabled):
            self._state_by_cc.pop(cc, None)

    def get_enabled_channels(self) -> List[str]:
        return sorted(self._enabled_cc, key=self._sort_key_cc)

    def reset_channel_state(self, channel_id: str) -> None:
        cc = str(channel_id or "").strip()
        if cc:
            self._state_by_cc.pop(cc, None)

    def reset_all_state(self) -> None:
        self._state_by_cc.clear()

    def _normalize_input(self, value: Any, length: int) -> np.ndarray:
        if isinstance(value, np.ndarray):
            arr = np.asarray(value, dtype=np.float64)
            if arr.ndim == 0:
                return np.full(max(1, length), float(arr), dtype=np.float64)
            arr = arr.reshape(-1)
            if length > 0 and arr.size != length:
                raise ValueError(f"dimensione non valida: atteso {length}, ottenuto {arr.size}")
            return np.ascontiguousarray(arr, dtype=np.float64)

        if np.isscalar(value):
            return np.full(max(1, length), float(value), dtype=np.float64)

        arr = np.asarray(value, dtype=np.float64).reshape(-1)
        if arr.ndim == 0:
            return np.full(max(1, length), float(arr), dtype=np.float64)
        if length > 0 and arr.size != length:
            raise ValueError(f"dimensione non valida: atteso {length}, ottenuto {arr.size}")
        return np.ascontiguousarray(arr, dtype=np.float64)

    def _normalize_output(self, value: Any, length: int) -> np.ndarray:
        n = max(1, int(length))
        if isinstance(value, np.ndarray):
            arr = np.asarray(value, dtype=np.float64).reshape(-1)
        elif np.isscalar(value):
            return np.full(n, float(value), dtype=np.float64)
        else:
            arr = np.asarray(value, dtype=np.float64).reshape(-1)
        if arr.size == n:
            return np.ascontiguousarray(arr, dtype=np.float64)
        if n > 1 and arr.size == (n - 1):
            return np.ascontiguousarray(np.pad(arr, (0, 1), mode="edge"), dtype=np.float64)
        if arr.size > n:
            return np.ascontiguousarray(arr[:n], dtype=np.float64)
        raise ValueError(f"dimensione non valida: atteso {n}, ottenuto {arr.size}")

    def _guess_length(self, inputs: Dict[str, Any]) -> int:
        for val in (inputs or {}).values():
            if isinstance(val, np.ndarray) and val.ndim > 0 and val.size > 0:
                return int(val.reshape(-1).size)
            try:
                arr = np.asarray(val)
                if arr.ndim > 0 and arr.size > 0:
                    return int(arr.reshape(-1).size)
            except Exception:
                continue
        return 1

    def evaluate(self, inputs: Dict[str, Any], fs_hz: float, fill_value: float = 0.0) -> Tuple[Dict[str, np.ndarray], Dict[str, str]]:
        context: Dict[str, Any] = {}
        errors: Dict[str, str] = dict(self._compile_errors)
        outputs: Dict[str, np.ndarray] = {}

        n = self._guess_length(inputs)
        for key, val in (inputs or {}).items():
            try:
                context[str(key)] = self._normalize_input(val, n)
            except Exception as exc:
                errors[str(key)] = f"Input non valido: {exc}"
        try:
            context["Fs"] = float(fs_hz)
        except Exception:
            context["Fs"] = 0.0

        default_arr = np.full(max(1, n), float(fill_value), dtype=np.float64)

        for cc in sorted(self._formula_by_cc.keys(), key=self._sort_key_cc):
            outputs[cc] = default_arr.copy()
            if cc not in self._enabled_cc:
                context[cc] = default_arr.copy()

        for cc in self._eval_order:
            if cc not in self._enabled_cc:
                continue
            comp = self._compiled_by_cc.get(cc)
            if comp is None:
                continue
            missing = [d for d in comp.deps if d != "Fs" and d not in context]
            if missing:
                errors[cc] = "Variabili mancanti: " + ", ".join(sorted(missing))
                context[cc] = default_arr.copy()
                outputs[cc] = context[cc]
                continue

            try:
                self._runtime_eval_cc = cc
                self._runtime_eval_len = n
                if comp.kind == "expr":
                    val = eval(comp.code, self._allowed_eval_globals(), dict(context))
                else:
                    fn = comp.func
                    if fn is None:
                        raise RuntimeError("Funzione non disponibile.")
                    kwargs = {arg: context[arg] for arg in comp.func_args}
                    val = fn(**kwargs)
                try:
                    arr = self._normalize_output(val, n)
                except Exception:
                    arr = self._normalize_input(val, n)
                if not np.all(np.isfinite(arr)):
                    arr = np.nan_to_num(arr, nan=float(fill_value), posinf=float(fill_value), neginf=float(fill_value))
                context[cc] = arr
                outputs[cc] = arr
                if cc in errors:
                    errors.pop(cc, None)
            except Exception as exc:
                errors[cc] = f"Errore runtime: {exc}"
                context[cc] = default_arr.copy()
                outputs[cc] = context[cc]
            finally:
                self._runtime_eval_cc = None
                self._runtime_eval_len = 1

        return outputs, errors
