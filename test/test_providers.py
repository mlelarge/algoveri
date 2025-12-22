from src.llm.providers import GeminiProvider, OpenAICompatibleProvider, VLLMProvider



def test_gemini():
    provider = GeminiProvider()
    mtchat = provider.new_chat(model="gemini-3-flash-preview", system_prompt="You are a helpful assistant.")
    
    res = mtchat.send_message("Hello, how are you?")
    print(res['text'])
    res = mtchat.send_message("Can you write a short poem about the stars?")
    print(res['text'])
    print(mtchat.get_total_tokens())
    print(mtchat.get_total_tokens().total_tokens)
    print(type(mtchat.get_total_tokens().total_tokens))

def test_openai():
    provider = OpenAICompatibleProvider()
    mtchat = provider.new_chat(model="gpt-4o", system_prompt="You are a helpful assistant.")
    
    res = mtchat.send_message("Hello, how are you?")
    print(res['text'])
    res = mtchat.send_message("Can you write a short poem about the stars?")
    print(res['text'])
    print(mtchat.get_total_price())

def test_vllm():
    provider = VLLMProvider(endpoint="http://della-j17g2:56053/v1")
    mtchat = provider.new_chat(model='/scratch/gpfs/ARORA/haoyu/Qwen3-235B-A22B-Instruct-2507', system_prompt="You are a helpful assistant.")
    
    #res = mtchat.send_message("Hello, how are you?")
    #print(res['text'])
    #res = mtchat.send_message("Illustrate what is the advantange of Rust programming language, compared with other popular programming languages like C++, Java, Python, and Go. Provide a detailed explanation.")
    #print(res['text'])
    #print(res)
    res = mtchat.send_message("There are $8!=40320$ eight-digit positive integers that use each of the digits $1,2,3,4,5,6,7,8$ exactly once. Let $N$ be the number of these integers that are divisible by 22. Find the difference between $N$ and 2025.")
    print(res['text'])
    print(res)


if __name__ == "__main__":
    test_vllm()
