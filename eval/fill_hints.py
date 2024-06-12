import argparse
import sglang as sgl
from sglang import OpenAI, Anthropic, VertexAI, Runtime, assistant, gen, set_default_backend, system, user

from sys_prompts import *
from utils import (
    extract_code_from_llm_output,
    run_dafny,
    is_dafny_verified,
    check_no_cheating,
    save_result,
)


# Function adapted from: https://github.com/ChuyueSun/Clover/blob/main/clover/clover.py
@sgl.function
def fill_hints(s, model, test_file, dafny_path, feedback_turn):
    program_path = f"../DafnyBench/dataset/hints_removed/{test_file}"

    with open(program_path, "r") as file:
        body = file.read()
    
    s += system(SYS_DAFNY)
    s += user(GEN_HINTS_FROM_BODY + body)
    body_with_hints = ""
    counter = 1

    # Give LLM multiple tries to reconstruct hints (& take into account Dafny feedback)
    for _ in range(feedback_turn):
        with s.copy() as tmp:
            tmp += assistant(gen("new_body_with_hints", max_tokens=4096, temperature=0.3))
            body_with_hints = extract_code_from_llm_output(tmp["new_body_with_hints"])
        s += assistant(body_with_hints)
        out, _ = run_dafny(body_with_hints, dafny_path)
        spec_preserved, no_avoid_verify = check_no_cheating(body, body_with_hints)

        if is_dafny_verified(str(out)) and spec_preserved and no_avoid_verify:
            save_result(model, test_file, counter, body_with_hints)
            return True
        
        with s.user():
            if not is_dafny_verified(str(out)):
                s += "This answer got Dafny verification error:\n" + str(out) + "\n"
                s += "Please try again by taking the Dafny feedback.\n"
            if not spec_preserved:
                s += "Please keep the preconditions and postconditions the same as the original program, or you fail the test.\n"
            if not no_avoid_verify:
                s += "Please don't use {:verify false} or assume false."
            counter += 1
    
    save_result(model, test_file, "failed", body_with_hints)
    return False


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Reconstruct hints for a Dafny program")
    parser.add_argument("--model", type=str, required=True)
    parser.add_argument("--test_file", type=str, required=True)
    parser.add_argument("--feedback_turn", type=int, default=10, help="# of feedback turns to give the LLM")
    parser.add_argument("--dafny_path", type=str, required=True, help="Path to the Dafny executable")
    args = parser.parse_args()
    
    # Model name examples: gpt-4o, gpt-4-turbo, gpt-3.5-turbo, claude-3-opus-20240229, gemini-1.5-pro-preview-0409, etc.
    if args.model.startswith("gpt"):
        set_default_backend(OpenAI(args.model))
    elif args.model.startswith("claude"):
        set_default_backend(Anthropic('claude-3-opus-20240229'))
    elif args.model.startswith("gemini"):
        set_default_backend(VertexAI(args.model))
    elif args.model.startswith("codellama-7b"):
        runtime = Runtime(model_path="codellama/CodeLlama-7b-Instruct-hf")
        set_default_backend(runtime)
    else:
        raise ValueError("Invalid model name")

    # Reconstruct hints, check if the program verifies
    verified = fill_hints(args.model, args.test_file, args.dafny_path, args.feedback_turn)
