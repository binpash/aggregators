import string, random
from  collections import defaultdict
from math import floor, sqrt, ceil 
import numpy as np

class RandomGenerator(): 
    def __init__(self, write_to_: str, file_size_target_: int,): 
        self.write_to = write_to_
        self.file_size_target = file_size_target_ 
        self.char_pool = string.ascii_lowercase + string.ascii_uppercase + string.digits + string.punctuation
    
    # def __init__(self, write_to_: str, file_size_target_: int, 
    #             identical_word_prob: float, identical_line_len_prob: float, 
    #             full_random: bool): 
    #     if not full_random:
    #         if identical_word_prob < 0 or identical_word_prob > 1: 
    #             raise ValueError("probability must be in range [0,1]", identical_word_prob)
            
    #         if identical_line_len_prob < 0 or identical_line_len_prob > 1: 
    #             raise ValueError("probability must be in range [0,1]", identical_line_len_prob)
        
    #     self.write_to = write_to_
    #     self.file_size_target = file_size_target_ 
    #     self.char_pool = string.ascii_lowercase + string.ascii_uppercase + string.digits + string.punctuation
    #     self.identical
        
    def generate_random_input_alphanumerical(self) -> str: 
            def generate_alphanumerical_helper(write_to: str, file_size: int) -> str: 
                bytes_written = 0 
                
                with open(write_to, "w") as rand_file: 
                    while bytes_written < file_size: 
                        line_len = random.randint(1,32) 
                        sentence = generate_random_sentence(line_len)
                        rand_file.write(sentence + '\n')
                        bytes_written += line_len + 1
    
            def generate_random_sentence(line_len: int) -> str:
                curr_line_len = 0 
                sentence = ""
                while curr_line_len < line_len: 
                    word_len = random.randint(1,line_len) 
                    word = ''.join(random.choices(self.char_pool, k=word_len))
                    sentence += word + " "
                    curr_line_len += len(word) + 1 

                return sentence 

            generate_alphanumerical_helper(self.write_to, self.file_size_target)
            return self.write_to
        
    def generate_sentence_len_distribution(self, distinct_len_prob: int, total_bytes: int, total_lines: int) -> list[int]:     
            num_of_same_len = ceil(total_lines * distinct_len_prob)
            num_of_uniq_len = total_lines - num_of_same_len
            print("splitting into ", total_lines, " distinc len: ", num_of_uniq_len, " same len: ", num_of_same_len)
            
            distribution = [0] * total_lines
            used_line_len = defaultdict(int)
            bytes_to_distribute = total_bytes
            
            identical_byte_val = random.randint(1, floor(total_bytes / total_lines))
            for idx in range(0, num_of_same_len): 
                distribution[idx] = identical_byte_val
                bytes_to_distribute -= identical_byte_val
                used_line_len[identical_byte_val] += 1 
            
            curr_sentence_idx = num_of_same_len
            lengths = [num for num in range(1, bytes_to_distribute)]
            dividers = sorted(random.sample(lengths, num_of_uniq_len - 1))
            r_end = bytes_to_distribute
            l_end_idx = len(dividers) - 1
            while l_end_idx > -1: 
                l_end = dividers[l_end_idx]
                curr_len = r_end - l_end
                if curr_len in distribution and l_end_idx > 1: 
                    print("identical found")
                    l_end_idx -= 1
                    l_end = dividers[l_end_idx]
                    sum_with_next = r_end - l_end
                    val_1 = random.randint(1, sum_with_next)
                    val_2 = sum_with_next - val_1
                    distribution[curr_sentence_idx] = val_1 
                    used_line_len[val_1] += 1
                    curr_sentence_idx += 1
                    curr_len = val_2 
                distribution[curr_sentence_idx] = curr_len 
                used_line_len[curr_len] += 1 
                r_end = l_end
                l_end_idx -= 1 
                curr_sentence_idx += 1
            
            distribution[-1] = r_end 
            total_repeated_line_length = sum([line for line in used_line_len.values() if line > 1])
            print(distribution)
            print("repeated_line_len", total_repeated_line_length)
            print("percentage of identical line lengths",total_repeated_line_length / total_lines)
            np.testing.assert_equal(np.sum(distribution), total_bytes)
            return distribution
    
    def generate_text(self, distinct_word_prob: int, line_distribution: list[int]) -> list[str]: 
        total_words = 0  
        used_word = defaultdict(int)
        word_len = defaultdict(int)
        word_to_use = defaultdict(list)

        # Determine randomly where whitespace should be placed and count words per sentence. 
        white_space = defaultdict(list)
        for idx, line_num in enumerate(line_distribution): 
            line_num_without_newline = line_num - 1 
            if line_num_without_newline == 1: 
                white_space[idx] = [0] # White-space line
            elif line_num_without_newline > 1: 
                number_of_ws = random.randint(1, round(line_num_without_newline / 2))
                potential_placements = [num for num in range(0, line_num_without_newline)]
                placements = sorted(random.sample(potential_placements, number_of_ws))
                
                # Populate word length to number of words dict for this line
                i = 0 
                while True: 
                    curr_word_len = 0 
                    while i not in placements and i in range(line_num_without_newline): 
                        curr_word_len += 1
                        i += 1 
                    if curr_word_len > 0: 
                        word_len[curr_word_len] += 1
                        total_words += 1
                    if i in range(line_num_without_newline): 
                        i += 1 
                    else: 
                        break
                    
                white_space[idx] += placements
            else: 
                white_space[idx] = [] # New line only 
        
        # Generate random words (with repeat when needed) mapping to word lengths.
        repeated_word = ceil(distinct_word_prob * total_words)
        print(word_len, "target words: ", repeated_word, "total words", total_words)
        for l, amt in word_len.items():
            if amt == 1: 
                word_to_use[l].append(self.get_random_word(l))
            elif amt > 1 and repeated_word > 0:
                if repeated_word - amt < 0: 
                    word = self.get_random_word(l)
                    word_to_use[l] = [word] * repeated_word
                    for _ in range(amt): 
                        word = self.get_random_word(l)
                        trial = 0
                        while word in word_to_use[l] and trial < 20:
                            word = self.get_random_word(l)
                            trial += 1 
                        word_to_use[l].append(word)
                else: 
                    word = self.get_random_word(l)
                    word_to_use[l] = [word] * amt
                repeated_word -= amt
            else: 
                for _ in range(amt): 
                    word = self.get_random_word(l)
                    trial = 0
                    while word in word_to_use[l] and trial < 20:
                        word = self.get_random_word(l)
                        trial += 1 
                    word_to_use[l].append(word)
                    
        
        # Generate text using word dict. 
        text = [0] * len(line_distribution)    
        idx = 0 
        for idx, ws_array in white_space.items(): 
            if len(ws_array) == 0: 
                str = "\n"
            else: 
                str = ""
                i = 0 
                while True: 
                    curr_word_len = 0 
                    while i not in ws_array and i in range(line_distribution[idx] - 1): 
                        curr_word_len += 1
                        i += 1 
                    if curr_word_len > 0:
                        word = word_to_use[curr_word_len][0] 
                        word_to_use[curr_word_len] = word_to_use[curr_word_len][1:]
                        used_word[word] += 1 
                    else: 
                        word = ""
                    str += word
                    if i in range(line_distribution[idx] - 1):   
                        str += " "
                        i += 1 
                    else: 
                        break
                str += '\n'
            
            text[idx] = str
            np.testing.assert_equal(len(str), line_distribution[idx])
                    
        total_repeated_word = sum([word for word in used_word.values() if word > 1])
        print(total_repeated_word, "repeated", total_words, "total words", total_repeated_word / total_words, "percentage")
        return text  
        
    def shuffle_text(self, text: list[int]) -> bool: 
        random.shuffle(text)
        return True
    
    def get_random_word(self, word_len: int) -> str: 
        word = ''.join(random.choices(self.char_pool, k=word_len))
        return word
        

if __name__ == "__main__":
    rand_generator = RandomGenerator("rand.txt", 100) 
    total_bytes = 10000
    total_lines = 80
    distinct_line_len_prob = 0.2
    distinct_word_prob = 0.4
    distribution = rand_generator.generate_sentence_len_distribution(distinct_line_len_prob, total_bytes, total_lines)
    text = rand_generator.generate_text(distinct_word_prob, distribution)        
    rand_generator.shuffle_text(text)
    