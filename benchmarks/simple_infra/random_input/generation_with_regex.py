import string, random, rstr, re
from  collections import defaultdict
from math import floor, ceil 
import numpy as np

class RandomGeneratorRegex(): 
    def __init__(self, write_to_: str, file_size_target_: int, file_line_target_: int, 
                match_prob_: float,  pattern_: str, use_regex_: bool): 
        if match_prob_ < 0 or match_prob_ > 1: 
            raise ValueError("probability must be in range [0,1]", match_prob_)
        
        if file_line_target_ > file_size_target_: 
            raise ValueError("cannot have more lines than byte", file_line_target_)
        
        self.write_to = write_to_
        self.file_size_target = file_size_target_ 
        self.file_line_target = file_line_target_
        self.match_prob = match_prob_
        self.pattern = pattern_ 
        self.use_regex = use_regex_
        self.char_pool = string.ascii_lowercase + string.ascii_uppercase + string.digits + string.punctuation
        
    def generate(self): 
        bytes_without_newline = self.file_size_target 
        target_pattern_match = ceil(self.match_prob * bytes_without_newline)
        matching_words = []
        if self.use_regex: 
            matching_words = self.generate_regex_matching_words(target_pattern_match)
        else: 
            matching_words = self.generate_word_matching_words(target_pattern_match) 
       
        non_matching_bytes = self.file_size_target - (len(" ".join(matching_words)) + 1)
        non_matching_words = self.generate_non_matching_words(non_matching_bytes) 
        
        text = self.shuffle_and_build_text(matching_words, non_matching_words)
        if self.write_to != "": 
            self.write_text_to_file(text)
        return  text
    
    def regex_percentage(self, file_path: str, regex_pattern: str) -> float:
        pattern = re.compile(regex_pattern)
        total_lines = 0
        matching_lines = 0

        with open(file_path, 'r') as file:
            for line in file:
                total_lines += 1
                if pattern.search(line): 
                    matching_lines += 1
        
        if total_lines == 0:
            return 0.0 
        percentage = (matching_lines / total_lines) * 100
        return percentage

    # Generate Word Arrays
    def generate_regex_matching_words(self, bytes: int) -> list[str]:
        target_bytes = bytes
        words = []
        while target_bytes > 0: 
            word_len = random.randint(1, target_bytes) 
            word = self.get_random_word_regex(word_len)
            target_bytes -= len(word) + 1 # Consider length for whitespace
            words.append(word)
        return words

    def generate_word_matching_words(self, bytes: int) -> list[str]:
        target_bytes = 0
        words = []
        while target_bytes <= bytes: 
            word = self.pattern
            target_bytes += len(word) + 1 # Consider length for whitespace
            words.append(word)
        return words
    
    def generate_non_matching_words(self, bytes: int) -> list[str]:
        target_bytes = bytes
        words = []
        while target_bytes > 0: 
            word_len = random.randint(1, ceil(target_bytes / self.file_line_target))
            if self.use_regex: 
                word = self.get_random_word_not_matching_regex(word_len)
            else: 
                word = self.get_random_word(word_len)
            target_bytes -= len(word) + 1 # Consider length for whitespace
            words.append(word)
        if len(" ".join(words)) < bytes: 
            words[-1] += " "
        return words 
    
    def shuffle_and_build_text(self, matches: list[str], non_matches: list[str]): 
        text = ""
        written_bytes = 0

        all_words = matches + non_matches 
        random.shuffle(all_words)
       
        nl_dividers = random.sample(range(1, len(all_words)), min(self.file_line_target - 1, len(all_words)-1))
        for index in sorted(nl_dividers, reverse=True):
            all_words.insert(index, "\n")

        text = " ".join(all_words).replace(" \n ", "\n").strip()
    
        return text
    
    # Helper functions and functions to get single word. 
    def write_text_to_file(self, text: list[str]):
         with open(self.write_to, "w") as rand_file:  
            for line in text: 
                rand_file.write(line)  
        
    def shuffle_text(self, text: list[int]) -> bool: 
        random.shuffle(text)
        return True
    
    def get_random_word_regex(self, word_len: int) -> str: 
        if self.pattern != "":
            len_left = word_len
            word = ""
            if "[" not in self.pattern: 
                r_pattern = "[" + self.pattern + "]"
            else: 
                r_pattern = self.pattern
                 
            while len_left > 0: 
                generate_len = min(len_left, 100)
                regex_with_word_len = r_pattern + "{" + str(generate_len) + "}"  
                regex = rf"{regex_with_word_len}"
                word += rstr.xeger(regex)
                len_left -= generate_len
        else: 
            word = ''.join(random.choices(self.char_pool, k=word_len))
        return word

    def get_random_word(self, word_len: int) -> str: 
        word = ''.join(random.choices(self.char_pool, k=word_len))
        return word
    
    def get_random_word_not_matching_regex(self, word_len: int) -> str: 
        if "[" not in self.pattern: 
            r_pattern = "[" + self.pattern + "]"
        else: 
            r_pattern = self.pattern
                
        pattern = re.compile(r_pattern) 
        word = ""
        while len(word) < word_len and word_len != 0:
            char = random.choice(self.char_pool)
            check_word = word + char
            if not pattern.search(check_word):
                word += char
        return word

if __name__ == "__main__":
    total_bytes = 500
    total_lines = 20
    r_match_prob = 0.5
    regex = "A-Za-z" # regex for specific word: \b{word}\b
    word = "light" # regex for specific word: \b{word}\b
    rand_generator = RandomGeneratorRegex("rand.txt", total_bytes, total_lines, r_match_prob, word, False) 
    rand_generator_r = RandomGeneratorRegex("rand.txt", total_bytes, total_lines, r_match_prob, regex, True) 
    rand_generator_r.generate()
    
    