"""
子词重写游戏：局面的SG值/结局由递归计算，并由确定型有限状态自动机（dfa）验证。

重写规则格式：
    无前后缀：{片段: [片段', ...]}
    有前后缀：{(前缀, 片段, 后缀): [(前缀', 片段', 后缀'), ...]}
局面是字符（str或tuple格式）组成的词。
"""
import itertools
import time
from collections import deque

from ACG import *
from FSA import *

OUTCOME = True
"""计算结局代替SG值"""

TERMINAL_SG = 0
"""终局的SG值"""

PRINT_KEY_ONLY = False
"""只打印关键信息"""

TEST_SIZE = 12
"""测试后缀的最大长度"""

MAX_STATE_NUM = 500
"""自动机的状态数上限"""

if TERMINAL_SG == 0:
    OUTPUT_PATH = "results\\common\\nfa.txt"
    """输出txt文件的地址"""

    CLASSES_OUTPUT_PATH = "results\\common\\nfa_classes.txt"
    """输出txt文件的地址"""

    KEY_OUTPUT_PATH = "results\\common\\nfa_key.txt"
    """关键信息的输出地址"""

    IMAGE_PATH = "results\\common\\game_resolvable_image.png"

else:
    OUTPUT_PATH = "results\\common\\misere_nfa.txt"
    CLASSES_OUTPUT_PATH = "results\\common\\misere_nfa_classes.txt"
    KEY_OUTPUT_PATH = "results\\common\\misere_nfa_key.txt"
    IMAGE_PATH = "results\\common\\misere_game_resolvable_image.png"


def mex(sg_set):
    """mex函数（OUTCOME为True时只区分0与非0）"""

    if OUTCOME:
        return 1 if 0 in sg_set else 0
    else:
        now_mex = 0
        while now_mex in sg_set:
            now_mex += 1
        return now_mex


def sg_str(sg):
    """SG值的字符串（OUTCOME为True时只区分P局面与N局面）"""
    if OUTCOME:
        return "P" if sg == 0 else "N"
    else:
        return str(sg)


def bidim(digit: str):
    """二进制维数"""
    if len(digit) == 1:
        if digit == "1":
            return 1
        elif digit in "23":
            return 2
        elif digit in "4567":
            return 3
        elif digit in "89abcdef":
            return 4
        else:
            return 0
    else:
        return max(bidim(d) for d in digit)


def prefix_str(oxword):
    """将ox词前缀转换成元组格式"""

    # 拆分出标签
    tag = ""
    while oxword[:1] not in "ox":
        tag += oxword[:1]
        oxword = oxword[1:]

    word = tuple(len(o_serie) for o_serie in oxword.split("x"))

    if len(word) == 1:
        text = f"({f"{tag};" if tag else ""}+{word[0]}+)"
    elif len(word) == 2:
        text = (f"({f"{tag};" if tag else ""}"
                f"{f"+{word[0]};" if word[0] else ""}"
                f"{f"{word[-1]}+" if word[-1] else ""})")
    else:
        text = (f"({f"{tag};" if tag else ""}"
                f"{f"+{word[0]};" if word[0] else ""}"
                f"{",".join(str(heap) for heap in word[1:-1])};"
                f"{f"{word[-1]}+" if word[-1] else ""})")

    return text


def enum_multiheap(max_size, heap_num=None, min_heap=1):
    """枚举局面（降序排列的正整数元组）"""

    if type(heap_num) is int:

        if heap_num > max_size:
            return

        if heap_num == 0:
            yield ()
        elif heap_num == 1:
            for heap in range(min_heap, max_size + 1):
                word = (heap,)
                yield word
        else:
            for ex_word in enum_multiheap(max_size, heap_num - 1):

                for heap in range(min_heap, min(ex_word[-1], max_size - sum(ex_word)) + 1):
                    word = ex_word + (heap,)
                    yield word

    else:
        for l in (range(max_size + 1) if heap_num is None else heap_num):
            for word in enum_multiheap(max_size, l):
                yield word


def write(text, cover=False, key=False, output_path=None, key_output_path=None, end="\n"):
    """打印的同时写入输出文件"""

    text = str(text)

    if key or (not PRINT_KEY_ONLY):
        print(text, end=end)

    if not output_path:
        output_path = OUTPUT_PATH

    if not key_output_path:
        key_output_path = KEY_OUTPUT_PATH

    if output_path:
        with open(output_path, "w" if cover else "a") as file:
            file.write(text + end)
    if key:
        if key_output_path:
            with open(key_output_path, "w" if cover else "a") as key_file:
                key_file.write(text + end)


class rewriting_game:
    """
    子词重写游戏
    """

    def __init__(self, rewrites: dict[tuple | str: list[str]], terminal_sg=0, charas=None,
                 prefixes=None, suffixes=None):

        self.rewrites = rewrites
        """
        游戏的重写规则
            无前后缀：{片段: 片段'}
            有前后缀：{(前缀, 片段, 后缀): (前缀', 片段', 后缀')}
        """

        self.prefixes = set(prefixes) if prefixes else None
        """合法局面所要求的前缀"""

        self.suffixes = set(suffixes) if suffixes else None
        """合法局面所要求的后缀"""

        if charas:
            self.charas = list(charas)
            """字符表"""
        else:
            # 字符表默认为重写规则与前后缀中出现的全部字符
            words = [word
                     for rule in self.enum_rules()
                     for word in self.rule_words(rule)]
            words += list(self.prefixes or []) + list(self.suffixes or [])
            self.charas = sorted_items({chara for word in words for chara in word})

        # 字符格式必须统一，否则后面的词与自动机运算会出错
        if len({type(chara) for chara in self.charas}) > 1:
            raise ValueError(f"字符格式不统一：{self.charas}")

        # 前后缀默认为空词
        if self.prefixes is None:
            self.prefixes = {self.empty_word}
        if self.suffixes is None:
            self.suffixes = {self.empty_word}

        self.terminal_sg = terminal_sg
        """终局的SG值"""

        self.recorded_sg = {}
        """记录的SG值"""

    '''↓↓格式相关的属性：↓↓'''

    @property
    def empty_word(self):
        """空词"""
        return "" if all(type(chara) is str for chara in self.charas) else ()

    def join_charas(self, charas):
        """把字符序列拼成一个词"""
        if type(self.empty_word) is str:
            return "".join(charas)
        else:
            return tuple(charas)

    @staticmethod
    def append_chara(word, chara):
        """在词的末尾添加一个字符"""
        return word + chara if type(word) is str else word + (chara,)

    '''↓↓枚举其结构与规则：↓↓'''

    def enum_rules(self):
        """以生成器形式枚举所有重写规则的两侧"""

        for subword, next_subwords in self.rewrites.items():
            yield subword
            for next_subword in next_subwords:
                yield next_subword

    def enum_rewrites(self):
        """以生成器形式枚举所有重写规则"""

        for subword, next_subwords in self.rewrites.items():
            for next_subword in next_subwords:
                yield subword, next_subword

    @staticmethod
    def rule_words(rule):
        """一个重写规则中出现的词：片段本身，或(前缀, 片段, 后缀)中的三个词"""
        if type(rule) is str:
            return (rule,)
        else:
            return tuple(rule)

    def enum_midfixes(self, max_size):
        """枚举前后缀之间的全部词"""

        if type(self.empty_word) is str:
            # str格式的词直接用ACG的枚举函数
            yield from enum_words(self.charas, range(max_size + 1))
        else:
            for size in range(max_size + 1):
                for charas in itertools.product(self.charas, repeat=size):
                    yield self.join_charas(charas)

    def enum_words(self, max_size):
        """枚举局面（前后缀之间的全部词）"""

        for midfix in self.enum_midfixes(max_size):
            for prefix in self.prefixes:
                for suffix in self.suffixes:
                    yield prefix + midfix + suffix

    def enum_test_suffix(self, max_size):
        """枚举用于测试的后缀"""

        for midfix in self.enum_midfixes(max_size):
            for suffix in self.suffixes:
                yield midfix + suffix

    def write_describe(self, key=False):
        """打印描述"""

        if self.terminal_sg == 0:
            game_name = f"rewriting game"
        elif self.terminal_sg == 1:
            game_name = f"misere rewriting game"
        else:
            game_name = f"{self.terminal_sg}-misere rewriting game"

        write(f"Game: {game_name}", key=True)

        rule_text = "Legal moves: "
        for subword in sorted_items(self.rewrites.keys()):
            for next_subword in self.rewrites[subword]:
                if type(subword) is str:
                    rule_text += f"{subword}->{next_subword}; "
                else:
                    rule_text += (f"({", ".join(part for part in subword)})"
                                  f"->({", ".join(part for part in next_subword)}); ")

        write(rule_text, key=key)

    '''↓↓局面的SG（结局）值的递归计算：↓↓'''

    @staticmethod
    def replace_subword(word, subword, next_subword, start=0, end=None):
        """依次生成把word[start:end]中出现的subword都替换成next_subword后的结果"""

        if end is None:
            end = len(word)

        for i in range(start, end - len(subword) + 1):
            if word[i:i + len(subword)] == subword:
                yield word[:i] + next_subword + word[i + len(subword):]

    def get_next_words(self, word):
        """以生成器形式给出一个局面所有接下来的局面"""

        for subword, next_subword in self.enum_rewrites():

            # 无前后缀：片段可以出现在任意位置
            if type(subword) is str:
                yield from self.replace_subword(word, subword, next_subword)

            # 有前后缀：前缀与后缀固定在词首与词尾，片段替换后连同前后缀一起替换
            else:
                prefix, midfix, suffix = subword
                next_prefix, next_midfix, next_suffix = next_subword

                if len(word) < len(prefix) + len(midfix) + len(suffix):
                    continue
                if not (self.has_prefix(word, prefix) and self.has_suffix(word, suffix)):
                    continue

                mid_word = word[len(prefix):len(word) - len(suffix)]
                for next_mid_word in self.replace_subword(mid_word, midfix, next_midfix):
                    yield next_prefix + next_mid_word + next_suffix

    def calcul_word_sg(self, word):
        """计算SG（结局）值（不查记录）"""

        next_sg_set = {next_sg
                       for next_word in self.get_next_words(word)
                       if (next_sg := self.get_sg(next_word)) >= 0}

        if len(next_sg_set) == 0:
            return self.terminal_sg
        else:
            return mex(next_sg_set)

    def get_sg(self, word):
        """求SG（结局）值"""

        # 局面非法
        if not self.is_legal_word(word):
            return -1

        # 需计算的SG值
        sg = self.recorded_sg.get(word, None)
        if sg is None:
            sg = self.calcul_word_sg(word)
            self.recorded_sg[word] = sg

        return sg

    def has_prefix(self, word, prefix):
        """word是否以prefix为前缀"""

        return word[:len(prefix)] == prefix

    def has_suffix(self, word, suffix):
        """word是否以suffix为后缀"""

        return len(word) >= len(suffix) and word[len(word) - len(suffix):] == suffix

    def is_legal_word(self, word):
        """是合法局面"""

        return any(len(word) >= len(prefix) + len(suffix)
                   and self.has_prefix(word, prefix)
                   and self.has_suffix(word, suffix)
                   for prefix in self.prefixes
                   for suffix in self.suffixes)

    def prefix_cong_test(self, prefix1, prefix2, test_suffixes, print_progress=True):
        """用给定的测试后缀集测试两个前缀是否同余"""

        for suffix in test_suffixes:

            if self.get_sg(prefix1 + suffix) != self.get_sg(prefix2 + suffix):
                if print_progress:
                    print(f"  {prefix1} !~ {prefix2} for suffix {suffix}")
                return False

        if print_progress:
            print(f"  {prefix1} ~~ {prefix2} "
                  f"(G({prefix1})={self.get_sg(prefix1)}, G({prefix2})={self.get_sg(prefix2)})")

        return True

    '''↓↓根据归约给出确定具有某个SG（结局）值的局面的dfa：↓↓'''

    def get_sg_dfa(self, test_suffixes=None, max_sg=None, max_state_num=1000, max_recorded_sg=5000000,
                   print_progress=True):
        """根据归约给出确定具有某个SG值或OC值的局面的dfa"""

        if test_suffixes is None:
            test_suffixes = list(self.enum_test_suffix(TEST_SIZE))
            write(f"  ({len(test_suffixes)} test suffixes for size<={TEST_SIZE})")

        if OUTCOME:
            max_sg = 1
        elif max_sg is None:
            raise ValueError

        empty_word = self.empty_word

        # 各SG值对应的终止状态集合。初始状态是空前缀，每个前缀都是一条链上的状态。
        final_states_list = [{prefix for prefix in self.prefixes if self.get_sg(prefix) == sg}
                             for sg in range(max_sg + 1)]

        P_dfa = dfa(trans_map={(prefix[:i - 1], prefix[i - 1]): {prefix[:i]}
                               for prefix in self.prefixes
                               for i in range(1, len(prefix) + 1)},
                    charas=self.charas,
                    states=sorted_items({prefix[:i] for prefix in self.prefixes
                                         for i in range(len(prefix) + 1)}),
                    init_states={empty_word},
                    final_states=final_states_list[0],
                    name=f"U_0",
                    max_state_num=max_state_num)

        queue = deque(self.append_chara(prefix, chara)
                      for prefix in self.prefixes for chara in self.charas)

        # 已经记录的状态（用于快速查重）
        P_state_set = set(P_dfa.states)

        while len(queue) > 0:

            # 从队列中弹出新的状态
            now_state = queue.popleft()

            reduced = False

            # 检查该前缀是否可归约成已记录的状态
            for old_state in P_dfa.states:

                # 一个构成合法局面，另一个不构成，不能归约
                if self.is_legal_word(now_state) != self.is_legal_word(old_state):
                    continue

                # 归约成功
                if self.prefix_cong_test(old_state, now_state, test_suffixes, print_progress):
                    # 归约后该状态与旧状态合并，直接覆盖转变以保证P_dfa仍是确定的
                    P_dfa.trans_map[(now_state[:-1], now_state[-1])] = {old_state}
                    reduced = True

                    if print_progress:
                        print(f"    New reductive trans added: {now_state[:-1]}@{now_state[-1]}->{old_state}")

                    break

            if reduced:
                continue

            # 该前缀是一个未被记录的新状态，将其记入状态集
            if now_state not in P_state_set:
                P_dfa.states.append(now_state)
                P_state_set.add(now_state)

            # 是合法局面则记入终止状态集
            if self.is_legal_word(now_state):
                sg = self.get_sg(now_state)
                print(f"G({now_state})={sg}")

                if sg < len(final_states_list):
                    final_states_list[sg].add(now_state)
                else:
                    write(f"  \033[31mSG value {sg} exceeds max_sg={max_sg}!\033[0m", key=True)

                if print_progress:
                    print(f"    New {sg_str(sg)}-state added: {now_state}")

            # 平凡的转移
            P_dfa.add_trans((now_state[:-1], now_state[-1]), now_state)

            # 状态数溢出，停止搜索
            if len(P_dfa.states) > max_state_num:
                write(f"  \033[31mState number overflow (>{max_state_num})!\033[0m", key=True)

                if print_progress:
                    print(f"    remained states: {", ".join(word_str(state) for state in list(queue)[:100])},...")

                return None

            # 在前缀后加字符继续等待归约
            for chara in self.charas:
                queue.append(self.append_chara(now_state, chara))

            # 记录的SG数溢出，停止搜索
            if len(self.recorded_sg) > max_recorded_sg:
                write(f"  \033[31mRecorded SG overflow (number >{max_recorded_sg})!\033[0m", key=True)

                if print_progress:
                    print(f"    remained states: {", ".join(word_str(state) for state in list(queue)[:100])},...")
                return None

        # 终止状态在BFS之后统一更新（与final_states_list[0]一致）
        P_dfa.final_states = final_states_list[0]

        # 所有U_sg共用同一转变映射，只是终止状态不同
        sg_dfa_list = [P_dfa]
        for sg in range(1, max_sg + 1):
            sg_dfa_list.append(dfa(trans_map=P_dfa.trans_map,
                                   charas=self.charas,
                                   states=P_dfa.states,
                                   init_states=P_dfa.init_states,
                                   final_states=final_states_list[sg],
                                   name=f"U_{sg}",
                                   max_state_num=max_state_num))

        return sg_dfa_list

    '''↓↓由重写规则构造的dfa：↓↓'''

    def get_word_dfa(self, word):
        """只接受一个词的dfa"""
        return dfa.words_acceptor([word], charas=self.charas)

    def get_sigma_star_dfa(self):
        """字符表的Kleene星号Σ*的dfa（单状态的自环）"""

        return dfa(trans_map={(0, chara): 0 for chara in self.charas},
                   charas=self.charas, states=[0], init_states={0}, final_states={0}, name="Σ*")

    def get_positions_dfa(self):
        """全体合法局面的dfa：前缀·Σ*·后缀"""

        positions_dfa = (dfa.words_acceptor(self.prefixes, charas=self.charas)
                         * self.get_sigma_star_dfa()
                         * dfa.words_acceptor(self.suffixes, charas=self.charas)).to_dfa()
        positions_dfa.name = "U"

        return positions_dfa

    def get_movables_dfa(self, positions_dfa=None):
        """全体可动局面的dfa（含有可重写片段且合法的局面）"""

        if positions_dfa is None:
            positions_dfa = self.get_positions_dfa()

        sigma_star = self.get_sigma_star_dfa()

        movables_dfa = dfa.words_acceptor([])
        for subword in self.rewrites:

            # 无前后缀：片段可以出现在任意位置
            if type(subword) is str:
                movables_dfa |= sigma_star * self.get_word_dfa(subword) * sigma_star

            # 有前后缀：前缀与后缀固定在词首与词尾，片段出现在中间
            else:
                prefix, midfix, suffix = subword
                movables_dfa |= (self.get_word_dfa(prefix)
                                 * sigma_star
                                 * self.get_word_dfa(midfix)
                                 * sigma_star
                                 * self.get_word_dfa(suffix))

        movables_dfa = movables_dfa.to_dfa() & positions_dfa
        movables_dfa.name = f"(U-T)"

        return movables_dfa

    def get_terminals_dfa(self):
        """全体终局的dfa"""

        positions_dfa = self.get_positions_dfa()
        terminals_dfa = positions_dfa - self.get_movables_dfa(positions_dfa)
        terminals_dfa.name = "T"

        return terminals_dfa

    def comp_rewrite_dfa(self, source_dfa, from_rule, to_rule):
        """对source_dfa施行一次重写规则，给出后继局面的自动机"""

        # 无前后缀：直接在任意位置重写
        if type(from_rule) is str:
            return source_dfa.comp_rewrite((from_rule, to_rule))

        # 有前后缀：先把前后缀去掉，重写中间的片段，再把新的前后缀加上
        prefix, midfix, suffix = from_rule
        next_prefix, next_midfix, next_suffix = to_rule

        midfix_fa = (source_dfa.left_quot(prefix)
                     .right_quot(suffix)
                     .comp_rewrite((midfix, next_midfix)))

        return self.get_word_dfa(next_prefix) * midfix_fa * self.get_word_dfa(next_suffix)

    def get_next_dfa(self, source_dfa, legal=True):
        """给出该dfa包含的全部局面的后继局面的dfa"""

        next_dfa = dfa.words_acceptor([])

        for subword, next_subword in self.enum_rewrites():
            next_dfa |= self.comp_rewrite_dfa(source_dfa, subword, next_subword)

        next_dfa = next_dfa.to_dfa()

        # 后继局面应当是合法局面
        if legal:
            next_dfa &= self.get_positions_dfa()

        next_dfa.name = f"next({source_dfa.name})"

        return next_dfa

    def get_prev_dfa(self, source_dfa, legal=True):
        """给出该dfa包含的全部局面的前驱局面的dfa"""

        prev_dfa = dfa.words_acceptor([])

        for subword, next_subword in self.enum_rewrites():
            prev_dfa |= self.comp_rewrite_dfa(source_dfa, next_subword, subword)

        prev_dfa = prev_dfa.to_dfa()

        # 前驱局面应当是合法局面
        if legal:
            prev_dfa &= self.get_positions_dfa()

        prev_dfa.name = f"prev({source_dfa.name})"

        return prev_dfa


# 是否倒序枚举局面
reverse = False

start_time = time.time()

write(f"Date: 2026/7/19", cover=True, key=True)
write(f"Params:", key=True)
write(f"  TEST_SIZE={TEST_SIZE}", key=True)
write(f"  MAX_STATE_NUM={MAX_STATE_NUM}", key=True)

game = rewriting_game(charas=["0", "1"],
                      rewrites={"0000": {"00"}, "1000": {"10"}, "1001": {"11"}},
                      prefixes={"1"},
                      suffixes={"1"})

for i in range(30):
    print(f"G(x{i}x) = {game.get_sg(f"1{"0"*i}1")}, G(x{i}xx) = {game.get_sg(f"1{"0"*i}11")}")

print(list(game.get_next_words("1001")))

sg_dfa_list = game.get_sg_dfa()
for sg_dfa in sg_dfa_list:
    print(sg_dfa.describe())

# 由重写规则构造的dfa
positions_dfa = game.get_positions_dfa()
movables_dfa = game.get_movables_dfa(positions_dfa)
terminals_dfa = game.get_terminals_dfa()
print(f"U: {len(positions_dfa.states)} states, "
      f"U-T: {len(movables_dfa.states)} states, "
      f"T: {len(terminals_dfa.states)} states")
print(f"next(U_0): {len(game.get_next_dfa(sg_dfa_list[0]).states)} states, "
      f"prev(U_0): {len(game.get_prev_dfa(sg_dfa_list[0]).states)} states")

# for index, game in enumerate(rewriting_game.enum_n_cross_games(max_n=6)):
#
#     # for index, ((index_L, index_R), game) in enumerate(misere_octal_game.enum_games(reverse=reverse, terminal_sg=1)):
#
#     game: rewriting_game
#     # game: misere_octal_game
#
#     game_start_time = time.time()
#     for _ in range(1):
#
#         write("=" * 50, key=True)
#         game.write_describe()
#
#         try:
#             P_dfa, N_dfa = game.get_sg_dfa(test_suffixes=test_suffixes, max_state_num=MAX_STATE_NUM)
#         except OverflowError:
#             P_dfa, N_dfa = None, None
#
#         # 自动机未找到
#         if P_dfa is None:
#             write(f"\033[31mOutcome-DFA state num overflowed (>{MAX_STATE_NUM})!\033[0m ", key=True)
#
#             continue
#
#         # 清空SG值记录，为自动机的计算腾出内存
#         game.recorded_sg = {}
#
#         # 各种状态的计数
#         class_nums = (len(P_dfa.final_states), len(N_dfa.final_states))
#
#         # 展示找到的自动机
#         write("-" * 50)
#         write(N_dfa)
#
#         try:
#             next_P_dfa = P_dfa.comp_rewrite([(subword, next_subword) for subword, next_subword in game.enum_rewrites()])
#             next_P_dfa.name = f"next({P_dfa.name})"
#
#             prev_P_dfa = P_dfa.comp_rewrite([(next_subword, subword) for subword, next_subword in game.enum_rewrites()])
#             prev_P_dfa.name = f"prev({P_dfa.name})"
#
#         # 自动机状态数溢出
#         except OverflowError:
#             write(f"\033[31mPrev/Next-DFA state number overflowed (>{50000})!\033[0m ", key=True)
#             continue
#
#         write("-" * 50)
#         write(f"Final/total state nums:")
#         write(f"  P: {len(P_dfa.final_states)}/{len(P_dfa.states)}")
#         write(f"  N: {len(N_dfa.final_states)}/{len(N_dfa.states)}")
#         write(f"  prev(P): {len(prev_P_dfa.final_states)}/{len(prev_P_dfa.states)}")
#         write(f"  next(P): {len(next_P_dfa.final_states)}/{len(next_P_dfa.states)}")
#
#         term_dfa = game.get_terminals_dfa()
#
#         # 需要满足的三个条件
#         conds = {"T": None, "0": None, "1": None}
#         cond_texts = {"T": f"T <= {"P" if game.terminal_sg == 0 else "N"}",
#                       "0": "next(P) <= N",
#                       "1": f"N{"" if game.terminal_sg == 0 else "\\T"} <= prev(P)"}
#
#         write("-" * 50)
#         write(f"Conditions:", key=True)
#
#         for cond_code in "T01":
#
#             cond = None
#             try:
#                 # 条件T：终局一定是P局面（misere规则则一定是N局面）
#                 if cond_code == "T":
#                     cond = (term_dfa <= P_dfa) if game.terminal_sg == 0 else (term_dfa <= N_dfa)
#
#                 # 条件0： P局面可达的一定是N局面，next(P) <= N
#                 elif cond_code == "0":
#                     cond = next_P_dfa <= N_dfa
#
#                 elif cond_code == "1":
#                     cond = (N_dfa if game.terminal_sg == 0 else (N_dfa - term_dfa)) <= prev_P_dfa
#
#             except OverflowError:
#                 cond = None
#
#             conds[cond_code] = cond
#
#             write(f"  {cond_texts[cond_code]}: "
#                   f"{"\033[32mTrue\033[0m" if cond else "\033[31mFalse\033[0m"}", key=True)
#
#             if not cond:
#                 break
#
#         if not all(conds.values()):
#             write("\033[31mFailed to prove!\033[0m "
#                   f"({len(N_dfa.states)} states)", key=True)
#
#         else:
#             write("\033[32mSucceed to prove!\033[0m "
#                   f"(P,N-class num={",".join(str(num) for num in class_nums)}, "
#                   f"sum class num={sum(class_nums)}, "
#                   f"state num={len(N_dfa.states)})", key=True)
