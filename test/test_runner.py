from pathlib import Path
import sys

from src.eval.verus_eval import VerusEval
from src.llm.providers import GeminiProvider, OpenAICompatibleProvider, VLLMProvider

from src.eval.runner import Runner

def test_runner_verus():
    llm_provider = GeminiProvider()
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    runner = Runner(llm_provider=llm_provider, language="verus", cfg_path=str(cfg_path), results_root="test_results/verus")

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

    res = runner.run_problem(problem_dir=str(problem_dir), max_rounds=15, model="gemini-3-flash-preview", debug=True)
    print(res)


if __name__ == "__main__":
    test_runner_verus()