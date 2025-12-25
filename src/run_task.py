from pathlib import Path
import sys
import argparse

from src.eval.verus_eval import VerusEval
from src.llm.providers import GeminiProvider, OpenAICompatibleProvider, VLLMProvider

from src.eval.runner import Runner

def run_task(args):
    if args.model.startswith("gemini"):
        llm_provider = GeminiProvider()
    elif args.model.lower().split('/')[-1].startswith("qwen"):
        assert args.url, "url must be provided"
        llm_provider = VLLMProvider(endpoint=args.url)
    else:
        raise ValueError(f"Unknown model {args.model}")
    
    cfg_path = Path(args.cfg_path)
    
    runner = Runner(llm_provider=llm_provider, language=args.language, cfg_path=str(cfg_path), results_root=f"test_results/{args.language}")

    # If stdin is piped, use that as the problem directory; otherwise use the default path.
    default_dir = "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/stack_push"
    problem_dir = default_dir
    try:
        if not sys.stdin.isatty():
            piped = sys.stdin.read().strip()
            if piped:
                problem_dir = piped
    except Exception:
        # fallback to default
        problem_dir = default_dir

    res = runner.run_problem(problem_dir=str(problem_dir), max_rounds=args.max_rounds, num_passes=args.num_passes, model=args.model, debug=True)
    print(res)


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("--model", type=str, default="gemini-3-flash-preview")
    argparser.add_argument("--max_rounds", type=int, default=15)
    argparser.add_argument("--num_passes", type=int, default=1)
    argparser.add_argument("--debug", action="store_true")
    argparser.add_argument("--cfg_path", type=str, default="/scratch/gpfs/ARORA/haoyu/algoveri/test/config_test.yaml")
    argparser.add_argument("--results_root", type=str, default="test_results/verus")
    argparser.add_argument("--language", type=str, default="verus")
    argparser.add_argument("--url", type=str, default="")
    args = argparser.parse_args()
    run_task(args)