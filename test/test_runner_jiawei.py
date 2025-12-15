from pathlib import Path

from src.eval.verus_eval import VerusEval
from src.llm.providers import GeminiProvider, OpenAICompatibleProvider, VLLMProvider

from src.eval.runner import Runner

def test_runner_verus():
    llm_provider = GeminiProvider()
    cfg_path = Path(__file__).resolve().parent / "config_jiawei_test.yaml"
    runner = Runner(llm_provider=llm_provider, language="verus", cfg_path=str(cfg_path), results_root="test_results/verus")
    res = runner.run_problem(problem_dir="/scratch/gpfs/ARORA/haoyu/jiawei/algoveri/algoveri_data/quick_sort", max_rounds=15, model="gemini-3-pro-preview", debug=True)
    print(res)

if __name__ == "__main__":
    test_runner_verus()