import time

from ACG import *
from FSA import *
import colorsys
from PIL import Image, ImageDraw, ImageFont
import os

OUTPUT_PATH = "result\\result.txt"
"""输出txt文件的地址"""

KEY_OUTPUT_PATH = "result\\key_result.txt"
"""关键信息的输出地址"""

PRINT_KEY_ONLY = False
"""只打印关键信息"""

OUTCOME = True
"""计算结局代替SG值"""

OB_STRING = False
"""字符串表示为ob格式"""


def mex(sg_list):
    """mex函数"""

    if OUTCOME:
        return 1 if any(sg == 0 for sg in sg_list) else 0
    else:
        now_mex = 0
        while now_mex in sg_list:
            now_mex += 1
        return now_mex


def sg_str(sg):
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


def image_init(game_range="partizan", image_type="resolvable"):
    """表示游戏类型的图像进行初始化"""

    if game_range == "partizan":
        table_width, table_height = 72, 72
    elif game_range == "impartial":
        table_width, table_height = 8, 64
    else:
        raise NotImplementedError

    image = Image.new("RGB", (16 + 8 * table_width + 160, 8 * table_height), GAME_TYPE_COLOR[image_type]["?"])

    font = ImageFont.truetype("C:/Windows/Fonts/timesbd.ttf", size=16)
    small_font = ImageFont.load_default(8)

    # 添加左右侧的Octal编码，占宽度16
    draw = ImageDraw.Draw(image)
    for index in range(table_height):
        code = f"0.{index // 8 % 8}{index % 8}" if index < 64 else f"4.{index % 8}"
        draw.text((0, index * 8 - 1), code, font=small_font, fill=(0, 0, 0))
        draw.text((16 + 8 * table_width + 2, index * 8 - 1), code, font=small_font, fill=(0, 0, 0))

    # 添加右侧的颜色注解
    draw = ImageDraw.Draw(image)
    for index, game_type in enumerate(GAME_TYPE_SYMBS[image_type]):
        draw.rectangle((16 + 8 * table_width + 16 + 8, 8 + index * 20,
                        16 + 8 * table_width + 16 + 16, 16 + index * 20),
                       fill=GAME_TYPE_COLOR[image_type][game_type])
        draw.text((16 + 8 * table_width + 16 + 20, 2 + index * 20), GAME_TYPE_TEXT[image_type][game_type], font=font,
                  fill=(0, 0, 0))

    return image


def image_renew(image: Image, indexes, game_type, image_type="resolvable"):
    """在reduc_image上记录当前的游戏类型"""

    if game_type == " ":
        return

    draw = ImageDraw.Draw(image)

    draw.rectangle((16 + 8 * indexes[0] + 1, 8 * indexes[1] + 1, 16 + 8 * indexes[0] + 6, 8 * indexes[1] + 6),
                   GAME_TYPE_COLOR[image_type][game_type])

    draw.rectangle((16 + 8 * indexes[1] + 1, 8 * indexes[0] + 1, 16 + 8 * indexes[1] + 6, 8 * indexes[0] + 6),
                   GAME_TYPE_COLOR[image_type][game_type])

    image.save(RESOLVABLE_IMAGE_PATH)
    # print(f"  (Image renewed and saved at {RESOLVABLE_IMAGE_PATH})")


def get_next_heaps(heap: int, legal_tooks) -> tuple:
    """以生成器形式给出对一个堆进行行动后所有得到的多重堆"""

    # 拿走took=heap个子，无剩余
    if heap in legal_tooks[0]:
        yield ()

    # 拿走took个子，剩余不拆分
    for took in legal_tooks[1]:
        if heap > took:
            left = heap - took
            yield (left,)

    # 拿走took个子，剩余分成两堆
    for took in legal_tooks[2]:
        if heap > took + 1:

            # 分成left1<=left2, left1+left2=heap-took两堆
            left12 = heap - took
            for left1 in range(1, left12 // 2 + 1):
                left2 = left12 - left1

                yield (left1, left2)

    # 拿走took个子，剩余分成三堆
    for took in legal_tooks[3]:
        if heap > took + 1:

            # 分成left1<=left2, left1+left2=heap-took两堆
            left123 = heap - took
            for left1 in range(1, left123 // 3 + 1):
                left23 = left123 - left1
                for left2 in range(left1, left23 // 2 + 1):
                    left3 = left23 - left2

                    yield (left1, left2, left3)


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


class misere_octal_game:
    """
    （超）misere规则的Octal游戏
    """

    def __init__(self, code="0.106", terminal_sg=0):

        self.code = code
        """游戏的编码，每个编码对应的游戏是唯一的。"""

        self.tags = [""]
        """标签"""

        self.tag_len = 0
        """标签长度"""

        self.legal_tooks = [set() for _ in range(4)]
        """记录博弈规则的列表：[拆分堆数: {拿取子数}]。"""

        self.terminal_sg = terminal_sg
        """终局的SG值"""

        self.recorded_sg = {}
        """记录的SG值"""

        self.renew_rule(code)

    def renew_rule(self, code):
        """根据编码更新游戏规则"""

        d_to_heapnums = {'0': [], '1': [0], '2': [1], '3': [0, 1],
                         '4': [2], '5': [0, 2], '6': [1, 2], '7': [0, 1, 2],
                         '8': [3], '9': [0, 3], 'a': [1, 3], 'b': [0, 1, 3],
                         'c': [2, 3], 'd': [0, 2, 3], 'e': [1, 2, 3], 'f': [0, 1, 2, 3]}
        """各位编码对应的可行的分成的堆数"""

        # 转为标准格式，小数点前为0，末尾没有0
        if code[:1] == ".":
            code = "0" + code
        while code[-1:] == "0":
            code = code[:-1]
        self.code = code

        d_list = [chara for chara in code if chara in d_to_heapnums]  # 去掉小数点并转为列表
        for took, d in enumerate(d_list):
            for heap_num in d_to_heapnums[d]:
                self.legal_tooks[heap_num].add(took)

    @staticmethod
    def enum_games(return_indexes=True, reverse=False, form="0.xxx|4.xx", terminal_sg=0):
        """枚举misere octal游戏的序号和编码"""

        if form == "0.xxx" or form == "0.xxx|4.xx":
            index_upb = (8 ** 3 + 8 ** 2) if "4.xx" in form else (8 ** 3)

            for index in (range(index_upb - 1, -1, -1) if reverse else range(index_upb)):
                code = f"0.{index // 64 % 8}{index // 8 % 8}{index % 8}" if index < 8 ** 3 else f"4.{index // 8 % 8}{index % 8}"

                if return_indexes:
                    yield (index % 8, index // 8), misere_octal_game(code, terminal_sg)
                else:
                    yield misere_octal_game(code, terminal_sg)

    @staticmethod
    def enum_algper_games():
        """枚举代数循环的misere octal游戏的序号和编码"""

        for code in ["0.145", "0.157", "0.175", "0.26", "0.355", "0.357", "0.516", "0.54", "0.724", "0.734"]:
            yield misere_octal_game(f"{code}", terminal_sg=1)

    @staticmethod
    def enum_wildquat_games():
        """枚举wild quaternary游戏"""
        for code in ["0.3102", "0.3122", "0.3123", "0.3312"]:
            yield misere_octal_game(f"{code}", terminal_sg=1)

    @staticmethod
    def enum_words(max_size, heap_num=None, min_heap=1):
        """枚举局面（降序排列的正整数元组）"""

        return enum_multiheap(max_size, heap_num, min_heap)

    def write_describe(self, key=False):
        """打印描述"""

        if self.terminal_sg == 0:
            game_name = f"octal game {self.code}"
        elif self.terminal_sg == 1:
            game_name = f"misere octal game {self.code}"
        else:
            game_name = f"{self.terminal_sg}-misere octal game {self.code}"

        write(f"Game: {game_name}", key=True)

        rule_text = "Legal moves: "
        for took in self.legal_tooks[0]:
            rule_text += f"({took})->(0); "
        for took in self.legal_tooks[1]:
            rule_text += f"(h+{took})->(h); "
        for took in self.legal_tooks[2]:
            rule_text += f"(h+{took})->(h1,h2); "
        for took in self.legal_tooks[3]:
            rule_text += f"(h+{took})->(h1,h2,h3); "

        write(rule_text, key=key)

    def get_next_words(self, word):
        """以生成器形式给出一个盘面所有接下来的盘面"""

        # 选中heap进行操作
        for i, chosen_heap in enumerate(word):

            # 操作得到的堆与其余的堆加起来
            for next_chosen_heap in get_next_heaps(chosen_heap, self.legal_tooks):
                yield word[:i] + next_chosen_heap + word[i + 1:]

    def calcul_word_sg(self, word: tuple):
        """计算不可分的SG（不查记录）"""

        next_sg_set = {self.get_sg(next_word) for next_word in self.get_next_words(word)}

        if len(next_sg_set) == 0:
            return self.terminal_sg

        else:
            sg = mex(next_sg_set)
            return sg

    def get_sg(self, word):
        """求SG值"""

        # 将字符串表示转回元组格式
        if type(word) is str:
            word = tuple(len(o_serie) for o_serie in word.split("x") if o_serie != "")

        word = tuple(sorted(word))

        # 重新排序以方便查记录
        word = tuple(heap for heap in sorted(word) if heap > 0)

        # 已记录SG值
        sg = self.recorded_sg.get(word, None)

        # 需计算的SG值
        if sg is None:
            sg = self.calcul_word_sg(word)
            self.recorded_sg[word] = sg

            # if len(self.recorded_sg) % 500000 == 0:
            #     print(f"  ({len(self.recorded_sg)} SG recorded)")

        return sg

    def prefix_in_prefix(self, subprefix, prefix):

        return prefix[:len(subprefix)] == subprefix

    @staticmethod
    def enum_test_suffix(max_size, heap_num=None):
        """枚举用于测试的后缀"""

        for multiheap in enum_multiheap(max_size, heap_num, min_heap=0 if OB_STRING else 1):
            for head in range(max_size - sum(multiheap) - len(multiheap)):
                suffix = head * "o" + "x" + "x".join("o" * heap for heap in multiheap) + "x"

                yield suffix

        # for serie in enum_int_partitions(range(size), min_diff=0):
        #     for head in range(size - sum(serie) - len(serie)):
        #         suffix=head * "o" + "x" + "x".join("o" * heap for heap in serie) + "x"
        #         print(suffix)
        #         yield suffix

    def get_sg_nfa(self, test_suffixes, max_state_num=1000, max_recorded_sg=5000000):
        """根据归约给出确定具有某个SG值或OC值的局面的nfa"""

        if not OUTCOME:
            raise NotImplementedError

        if type(self) is misere_octal_game:
            P_nfa = nfa(trans_map={("", "x"): {"x"}},
                        charas=["x", "o"],
                        states=["", "x"],
                        init_states={""},
                        final_states=set() if self.terminal_sg != 0 else {"x"},
                        name=f"P({self.code})")
            queue = ["xx", "xo"]
            spec_state_num = 1
            N_nfa_final_states = set() if self.terminal_sg == 0 else {"x"}
        elif type(self) is partizan_octal_game:
            P_nfa = nfa(trans_map={("", "L"): {"L"}, ("", "R"): {"R"}, ("L", "x"): {"Lx"}, ("R", "x"): {"Rx"}},
                        charas=["L", "R", "x", "o"],
                        states=["", "L", "R", "Lx", "Rx"],
                        init_states={""},
                        final_states=set() if self.terminal_sg != 0 else {"Lx", "Rx"},
                        name=f"P({self.code})")
            queue = ["Lxx", "Rxx", "Lxo", "Rxo"]
            spec_state_num = 3
            N_nfa_final_states = set() if self.terminal_sg == 0 else {"Lx", "Rx"}
        else:
            raise NotImplementedError

        while len(queue) > 0:

            # 从队列中弹出新的状态
            now_state = queue.pop(0)

            reduced = False

            # 检查该前缀是否直接等价于某个已记录的状态，是则添加转移
            for old_state in P_nfa.states[spec_state_num:]:
                if self.prefix_equiv(old_state, now_state):
                    P_nfa.add_trans((now_state[:-1], now_state[-1]), old_state)
                    # print(f"    New trivial trans added: {now_state[:-1]}·{now_state[-1]}->{old_state}")
                    reduced = True
                    break

            if reduced:
                continue

            # 检查该前缀是否可归约成已记录的状态（要求末位相等）
            for old_state in P_nfa.states[spec_state_num:]:
                if old_state[-1:] != now_state[-1:]:
                    continue

                if self.prefix_cong(old_state, now_state, test_suffixes):
                    P_nfa.add_trans((now_state[:-1], now_state[-1]), old_state)
                    # print(f"    New reductive trans added: {now_state[:-1]}·{now_state[-1]}->{old_state}")
                    reduced = True
                    break

            if reduced:
                continue

            # 该前缀是一个未被记录的新状态，将其记入状态集；如果sg值符合且末尾为x，则为终止状态
            P_nfa.states.append(now_state)
            if now_state[-1:] == "x":
                sg = self.get_sg(now_state)
                if sg == 0:
                    P_nfa.final_states.add(now_state)
                    # print(f"    New P-state added: {now_state}")
                elif sg == 1:
                    N_nfa_final_states.add(now_state)
                    # print(f"    New N-state added: {now_state}")
            # elif now_state[-1:] == "x":
            #     print(f"  G({now_state})={self.get_sg(now_state)}")

            # if len(P_nfa.states) % 100 == 0:
            #     print(f"  ({len(P_nfa.states)} states recorded, {len(queue)} states remained)")

            # 平凡的转移
            P_nfa.add_trans((now_state[:-1], now_state[-1]), now_state)

            # if len(P_nfa.states) + len(queue) > max_state_num:
            if len(P_nfa.states) > max_state_num:
                write(f"  \033[31mState number overflow (>{max_state_num})!\033[0m", key=True)
                # print(f"    remained states: {", ".join(queue[:100])},...")
                return None, None

            # 在前缀后加o和x继续等待归约
            queue.append(now_state + "x")
            queue.append(now_state + "o")
            # print(f"    prefix {now_prefix} irreducible, new state added")

            # 记录的SG数溢出，停止搜索
            if len(self.recorded_sg) > max_recorded_sg:
                write(f"  \033[31mRecorded SG overflow (number >{max_recorded_sg})!\033[0m", key=True)
                # print(f"    states: {", ".join(queue[:100])},...")
                return None, None
            # else:
            #     print(f"  ({len(queue)} states left: {", ".join(queue[:10])},...)")

        N_nfa = P_nfa.copy(name=f"N({self.code})")
        N_nfa.final_states = N_nfa_final_states

        return P_nfa, N_nfa

    def get_positions_nfa(self, tags=None):
        """全体合法局面的nfa"""

        if tags is None:
            tags = self.tags
        elif type(tags) is str:
            tags = [tags]

        positions_nfa = (nfa.words_acceptor([f"{tag}x" for tag in tags])
                         * (nfa.words_acceptor(["x", "o"]) * "*")
                         * nfa.words_acceptor("x"))
        positions_nfa.name = (f"U{f"_{"|".join(tag for tag in tags)}" if len(tags) < len(self.tags) else ""}"
                              f"({self.code})")
        return positions_nfa

    def get_movables_nfa(self, tags=None):
        """全体可动局面的nfa"""

        if tags is None:
            tags = self.tags
        elif type(tags) is str:
            tags = [tags]

        # 包含可动子词且是合法局面
        movables_nfa = (nfa.words_acceptor(f"{tags}")
                        * (nfa.words_acceptor(["x", "o"]) * "*")
                        * nfa.words_acceptor({word for word, _ in self.to_rewrite(tags)})
                        * (nfa.words_acceptor(["x", "o"]) * "*"))
        movables_nfa = movables_nfa & self.get_positions_nfa(tags)
        movables_nfa.name = (f"(U-T){f"_{"|".join(tag for tag in tags)}" if len(tags) < len(self.tags) else ""}"
                             f"({self.code})")

        return movables_nfa

    def get_terminals_nfa(self, tags=None):
        """全体终局的nfa"""

        if tags is None:
            tags = self.tags
        elif type(tags) is str:
            tags = [tags]

        terminals_nfa = self.get_positions_nfa(tags) - self.get_movables_nfa(tags)
        terminals_nfa.name = (f"T{f"_{"|".join(tag for tag in tags)}" if len(tags) < len(self.tags) else ""}"
                              f"({self.code})")

        return terminals_nfa

    def get_ndper(self, test_bifixes, max_sum_pt=40):
        """测试周期性"""

        # 维数
        for dim in [1, 2]:

            # 周期与预周期之和
            for sum_pt in range(1, max_sum_pt + 1):

                # 预周期
                for p in range(sum_pt):
                    t = sum_pt - p

                    if dim == 1:
                        midfix, next_midfix = f"{"o" * (p + t)}", f"{"o" * p}"
                    else:
                        midfix, next_midfix = f"{"o" * (p + t)}x{"o" * (p + t)}", f"{"o" * p}x{"o" * p}"

                    periodic = True
                    for (prefix, suffix) in test_bifixes:
                        word = prefix + midfix + suffix
                        next_word = prefix + next_midfix + suffix
                        if self.get_sg(word) != self.get_sg(next_word):
                            periodic = False
                            break

                    if periodic:
                        return (dim, p, t)
        return None

    @staticmethod
    def prefix_equiv(prefix1, prefix2):
        """两个前缀等价（只相差一个置换）"""

        if "x" not in prefix1 or "x" not in prefix2:
            return prefix1 == prefix2

        # 开闭相同
        if prefix1[-1] != prefix2[-1]:
            return False

        serie1 = [len(blank) for blank in prefix1.split("x")]
        serie2 = [len(blank) for blank in prefix2.split("x")]

        if serie1[-1] != serie2[-1]:
            return False

        for heap in set(serie1[:-1]) | set(serie2[:-1]):
            if (OB_STRING or heap > 0) and serie1[:-1].count(heap) != serie2[:-1].count(heap):
                return False

        return True

    def prefix_cong(self, prefix1, prefix2, test_suffixes):
        """用给定的测试后缀集测试两个前缀是否同余"""

        for suffix in test_suffixes:
            word1 = prefix1 + suffix
            word2 = prefix2 + suffix

            if self.get_sg(word1) != self.get_sg(word2):
                return False

        return True

    def to_rewrite(self, tags=None, reverse=False):
        """将行动规则转换成ox-词的重写（不考虑标签）"""

        rewrites = []

        for took in self.legal_tooks[0]:
            rewrites.append((f"x{took * "o"}x", "x"))
        for took in self.legal_tooks[1]:
            rewrites.append((f"x{took * "o"}o", "xo"))
        for took in self.legal_tooks[2]:
            rewrites.append((f"o{took * "o"}o", "oxo"))

        if reverse:
            rewrites = [(next_subword, subword) for (subword, next_subword) in rewrites]

        return rewrites

    def has_algper(self, word, params: tuple[int, int, int, int]):
        """测试某个词是否满足当前参数的代数循环性"""

        # 输入了多个词
        if type(word) is not tuple:
            words = word
            return all(self.has_algper(word, params) for word in words)

        s, t, sigma, tau = params

        # 将局面升序排列
        word = tuple(sorted(word))

        if len(word) == 0:
            return True

        # 循环区域的必要条件：足够远离原点
        # if sum(word) >= sigma:
        # if sum(word[-2:]) >= sigma:
        # if min(word[-2:])>=sigma:
        if word[-1] >= sigma:

            # 一维循环范围，足够接近某个棱
            if len(word) < 2 or word[-2] < s:
                reduced_word = word[:-1] + (word[-1] - t,)

            # 二维循环范围，足够远离各个棱
            else:
                reduced_word = word[:-2] + (word[-2] - tau, word[-1] - tau)

        # 不在循环范围，未打破循环
        else:
            return True

        # 某个堆变成负数说明参数不规范，看作打破循环
        if any(heap < 0 for heap in reduced_word):
            # print(f"  {params}: params irregular ({word}->{reduced_word})")
            return False

        # 两者SG值不相等则循环不成立
        return self.get_sg(word) == self.get_sg(reduced_word)

    def get_algper(self, max_sigma=30,  max_size=30):
        """测试代数循环性"""

        if type(self) is misere_octal_game:
            heap_per = detect_period([self.get_sg((heap, 1)) for heap in range(max_size + 1)])
        else:
            heap_per = detect_period([self.get_sg(("L", (heap, 1))) for heap in range(max_size + 1)])

        if heap_per is None:
            # print(f"  {self.code}: No heap-period detected")
            return None
        else:
            t = heap_per[1]
            # print(f"{self.code}: t={heap_per[1]} (heap-period={heap_per})")

        for sigma in range(1, max_sigma + 1):

            if sigma > max_size:
                continue

            for tau in range(1,max_sigma-sigma+1):

                for s in range(1, sigma // 2 + 1):

                    if self.has_algper(self.enum_words(max_size), (s, t, sigma, tau)):
                        return (s, t, sigma, tau)

        return None



class partizan_octal_game(misere_octal_game):
    """
    有偏的Octal游戏
    """

    def __init__(self, code, terminal_sg=0):

        self.code = code
        """游戏的编码，每个编码对应的游戏是唯一的。规则L，R的编码用:隔开。"""

        self.tags = ["L", "R"]
        """标签，表示玩家及其对应的规则"""

        self.tag_len = 1
        """标签长度"""

        self.next_tag = {"L": "R", "R": "L"}
        """每个标签轮到的下一标签"""

        self.legal_tooks = {"L": [set() for _ in range(4)], "R": [set() for _ in range(4)]}
        """记录博弈规则的字典，格式为{标签: [拆分堆数: {拿取子数}]}。"""

        self.terminal_sg = terminal_sg
        """终局的SG值"""

        self.recorded_sg = {}
        """记录的SG值"""

        self.renew_rule(code)

        self.unmovable_heaps = self.get_unmovable_heaps()
        """无法移动的堆"""


    def enum_words(self, max_size, heap_num=None, min_heap=1):
        """枚举局面（降序排列的正整数元组）"""

        for body in enum_multiheap(max_size,heap_num,min_heap):
            for tag in self.tags:
                yield (tag, body)


    def renew_rule(self, code: str):
        """根据编码更新游戏规则"""

        d_to_heapnums = {'0': [], '1': [0], '2': [1], '3': [0, 1],
                         '4': [2], '5': [0, 2], '6': [1, 2], '7': [0, 1, 2],
                         '8': [3], '9': [0, 3], 'a': [1, 3], 'b': [0, 1, 3],
                         'c': [2, 3], 'd': [0, 2, 3], 'e': [1, 2, 3], 'f': [0, 1, 2, 3]}
        """各位编码对应的可行的分成的堆数"""

        # 转为标准格式，小数点前为0，末尾没有0
        code_L, code_R = code.split(":")
        code_dict = {"L": code_L, "R": code_R}

        for tag in self.tags:
            if code_dict[tag][:1] == ".":
                code_dict[tag] = "0" + code_dict[tag]
            while code_dict[tag][-1:] == "0":
                code_dict[tag] = code_dict[tag][:-1]

            d_list = [chara for chara in code_dict[tag] if chara in d_to_heapnums]  # 去掉小数点并转为列表

            for took, d in enumerate(d_list):
                for heap_num in d_to_heapnums[d]:
                    self.legal_tooks[tag][heap_num].add(took)

        self.code = f"{code_dict["L"]}:{code_dict["R"]}"

    @staticmethod
    def enum_games(return_indexes=True, reverse=False, form="0.xx|4.x", terminal_sg=0):
        """枚举partizan octal游戏的序号和编码"""

        if form == "0.xx" or form == "0.xx|4.x":
            index_L_upb = 72 if "4.x" in form else 64

            for index_L in (range(index_L_upb - 1, -1, -1) if reverse else range(index_L_upb)):
                code_L = f"0.{index_L // 8 % 8}{index_L % 8}" if index_L < 64 else f"4.{index_L % 8}"

                for index_R in (range(index_L, -1, -1) if reverse else range(index_L + 1)):

                    code_R = f"0.{index_R // 8 % 8}{index_R % 8}" if index_R < 64 else f"4.{index_R % 8}"
                    code = f"{code_L}:{code_R}"

                    if return_indexes:
                        yield (index_L, index_R), partizan_octal_game(code, terminal_sg)
                    else:
                        yield partizan_octal_game(code, terminal_sg)

        else:
            raise NotImplementedError

    @staticmethod
    def prefix_equiv(prefix1, prefix2):
        """两个前缀等价（只相差一个置换）"""

        if "x" not in prefix1 or "x" not in prefix2:
            return prefix1 == prefix2

        # 标签相同
        if prefix1[0] != prefix2[0]:
            return False

        # 开闭相同
        if prefix1[-1] != prefix2[-1]:
            return False

        serie1 = [len(blank) for blank in prefix1[1:].split("x")]
        serie2 = [len(blank) for blank in prefix2[1:].split("x")]

        if serie1[-1] != serie2[-1]:
            return False

        for heap in set(serie1[:-1]) | set(serie2[:-1]):
            if (OB_STRING or heap > 0) and serie1[:-1].count(heap) != serie2[:-1].count(heap):
                return False

        return True

    def get_unmovable_heaps(self):
        """无法移动的堆"""

        unmovable_heaps = {"L": set(), "R": set()}
        for tag in self.tags:
            for heap in range(10):

                word = (tag, (heap,))
                next_words = list(self.get_next_words(word))

                # print(f"{word} -> {next_words}")

                if len(next_words) == 0:
                    unmovable_heaps[tag].add(heap)

        # print(f"unmovable_heaps={unmovable_heaps}")
        return unmovable_heaps

    @property
    def code_L(self):
        return self.code.split(":")[0]

    @property
    def code_R(self):
        return self.code.split(":")[1]

    @property
    def dicotic(self):
        """是否dicotic"""
        return self.unmovable_heaps["L"] == self.unmovable_heaps["R"]

    @property
    def impartial(self):
        """是否无偏"""
        return self.code_L == self.code_R

    @property
    def dominance(self):
        """支配性"""
        if all(set(self.legal_tooks["R"][n]).issubset(set(self.legal_tooks["L"][n])) for n in [1, 2]):
            if set(self.legal_tooks["R"][0]).issubset(set(self.legal_tooks["L"][0])):
                return "strict-"
            else:
                return ""
        else:
            return "non-"

    def write_describe(self, key=False):
        """打印描述"""

        if self.terminal_sg == 0:
            game_name = f"partizan octal game {self.code}"
        elif self.terminal_sg == 1:
            game_name = f"partizan misere octal game {self.code}"
        else:
            game_name = f"partizan {self.terminal_sg}-misere octal game {self.code}"

        write(f"Game: {game_name}", key=True)

        property_text = "Properties: "
        property_text += "dicotic, " if self.dicotic else "non-dicotic, "
        property_text += "impartial, " if self.impartial else "partizan, "
        property_text += f"{self.dominance}dominant, "
        property_text += f"min/max bidim={min(bidim(code) for code in self.code.split(":"))}/{bidim(self.code)}"

        write(property_text, key=True)

        write(f"Legal moves:", key=key)
        for tag in self.tags:
            rule_text = f"  {tag}: "
            # for took in self.legal_tooks[tag][0]:
            #     rule_text += f"({took})->(0); "
            # for took in self.legal_tooks[tag][1]:
            #     rule_text += f"(h+{took})->(h); "
            # for took in self.legal_tooks[tag][2]:
            #     rule_text += f"(h+{took})->(h1,h2); "
            # for took in self.legal_tooks[tag][3]:
            #     rule_text += f"(h+{took})->(h1,h2,h3); "

            for subword, next_subword in self.to_rewrite(tag):
                rule_text += f"{subword}->{next_subword}, "

            write(rule_text, key=key)

    def get_next_words(self, word):
        """以生成器形式给出一个盘面所有接下来的盘面"""

        if type(word) is not tuple or type(word[0]) is not str:
            raise ValueError

        tag, body = word
        next_tag = self.next_tag[tag]

        # 选中heap进行操作
        for i, chosen_heap in enumerate(body):

            # 操作得到的堆与其余的堆加起来
            for next_chosen_heap in get_next_heaps(chosen_heap, self.legal_tooks[tag]):
                next_body = body[:i] + next_chosen_heap + body[i + 1:]

                yield (next_tag, next_body)

    def get_sg(self, word):
        """求SG值"""

        if type(word) is str:
            tag = word[:1]

            body = tuple(len(o_serie) for o_serie in word[1:].split("x") if o_serie != "")
        else:
            tag, body = word

        # 去掉双方都无法移动的堆
        if self.unmovable_heaps is not None:
            new_body = tuple(heap for heap in body if
                             ((heap not in self.unmovable_heaps["L"]) or (heap not in self.unmovable_heaps["R"])))

            body = new_body

        # 重新排序
        body = tuple(sorted(body))
        word = (tag, body)

        # 查找SG值记录
        sg = self.recorded_sg.get(word, None)

        # 没有记录则进行计算
        if sg is None:
            sg = self.calcul_word_sg(word)
            self.recorded_sg[word] = sg

        return sg

    def to_rewrite(self, tags=None, reverse=False):
        """将行动规则转换成ox-词的重写（不考虑标签）"""

        if tags is None:
            tags = self.tags

        elif type(tags) is str:
            tags = [tags]

        rewrites = []

        for tag in tags:
            for took in self.legal_tooks[tag][0]:
                rewrites.append((f"x{took * "o"}x", "x"))
            for took in self.legal_tooks[tag][1]:
                rewrites.append((f"x{took * "o"}o", "xo"))
            for took in self.legal_tooks[tag][2]:
                rewrites.append((f"o{took * "o"}o", "oxo"))

        if reverse:
            rewrites = [(next_subword, subword) for (subword, next_subword) in rewrites]

        return rewrites

    def has_algper(self, word, params: tuple[int, int, int, int]):
        """测试某个词是否满足当前参数的代数循环性"""

        # 输入了多个词
        if type(word) is not tuple:
            words = word
            return all(self.has_algper(word, params) for word in words)

        tag, body=word
        s, t, sigma, tau = params

        # 将局面升序排列
        body = tuple(sorted(body))

        if len(body) == 0:
            return True

        # 循环区域的必要条件：足够远离原点
        # if sum(word) >= sigma:
        # if sum(word[-2:]) >= sigma:
        # if min(word[-2:])>=sigma:
        if body[-1] >= sigma:

            # 一维循环范围，足够接近某个棱
            if len(body) < 2 or body[-2] < s:
                reduced_body = body[:-1] + (body[-1] - t,)

            # 二维循环范围，足够远离各个棱
            else:
                reduced_body = body[:-2] + (body[-2] - tau, body[-1] - tau)

        # 不在循环范围，未打破循环
        else:
            return True

        # 某个堆变成负数说明参数不规范，看作打破循环
        if any(heap < 0 for heap in reduced_body):
            # print(f"  {params}: params irregular ({word}->{reduced_word})")
            return False

        # 两者SG值不相等则循环不成立
        return self.get_sg(word) == self.get_sg(tag+reduced_body)



OUTCOME = True

TERMINAL_SG = 1

if TERMINAL_SG == 0:
    OUTPUT_PATH = "result\\partizan_octal\\nfa.txt"
    """输出txt文件的地址"""

    CLASSES_OUTPUT_PATH = "result\\partizan_octal\\nfa_classes.txt"
    """输出txt文件的地址"""

    KEY_OUTPUT_PATH = "result\\partizan_octal\\nfa_key.txt"
    """关键信息的输出地址"""

    RESOLVABLE_IMAGE_PATH = "result\\partizan_octal\\game_resolvable_image.png"

else:
    OUTPUT_PATH = "result\\partizan_octal\\misere_nfa.txt"
    CLASSES_OUTPUT_PATH = "result\\partizan_octal\\misere_nfa_classes.txt"
    KEY_OUTPUT_PATH = "result\\partizan_octal\\misere_nfa_key.txt"
    RESOLVABLE_IMAGE_PATH = "result\\partizan_octal\\misere_game_resolvable_image.png"

# OUTPUT_PATH = "result\\impartial_misere_octal\\algper_nfa.txt"
# """输出txt文件的地址"""
#
# CLASSES_OUTPUT_PATH = "result\\impartial_misere_octal\\algper_nfa_classes.txt"
# """输出txt文件的地址"""
#
# KEY_OUTPUT_PATH = "result\\impartial_misere_octal\\algper_nfa_key.txt"
# """关键信息的输出地址"""
#
# RESOLVABLE_IMAGE_PATH = "result\\impartial_misere_octal\\algper_game_resolvable_image.png"

GAME_TYPE_DICT = {"resolvable": {}}

GAME_TYPE_SYMBS = {"resolvable": "VxX "}
GAME_TYPE_COLOR = {"resolvable": {" ": (255, 255, 255),  # 平凡
                                  "V": (128, 255, 128),  # 成功
                                  "x": (255, 0, 0),  # 失败
                                  "X": (0, 0, 0),  # 非循环
                                  "?": (255, 255, 255), }  # 未计算（同时也是背景色）
                   }
GAME_TYPE_TEXT = {"resolvable": {" ": "trivial",  # 平凡
                                 "V": "DFA proved",  # 成功
                                 "x": "DFA not proved",  # 失败
                                 "X": "DFA not found",  # 非循环
                                 "?": "not calculated", }  # 未计算
                  }

TEST_SIZE = 30
MAX_STATE_NUM = 500
# MAX_STATE_NUM = 1000

if os.path.exists(RESOLVABLE_IMAGE_PATH):
    resolvable_image = Image.open(RESOLVABLE_IMAGE_PATH)
else:
    resolvable_image = image_init()
    resolvable_image.save(RESOLVABLE_IMAGE_PATH)

write(f"Date: 2026/7/19", cover=True, key=True)
write(f"Params:", key=True)
write(f"  TEST_SIZE={TEST_SIZE}", key=True)
write(f"  MAX_STATE_NUM={MAX_STATE_NUM}", key=True)

# 是否倒序枚举局面
reverse = False

test_suffixes = list(partizan_octal_game.enum_test_suffix(TEST_SIZE))
write(f"  ({len(test_suffixes)} test suffixes for size<={TEST_SIZE})")

test_bifix = [(tag + f"x{"o" * i}", suffix) for tag in "LR"
              for suffix in test_suffixes
              for i in range(min(TEST_SIZE - len(suffix) - 1,
                                 len(suffix.split("x")[0]) + 1))]

N_nfa_equiv_class = {}

recorded_N_nfa = {}
recorded_class_nums = {}
recorded_game_type = {}


if TERMINAL_SG == 0:

    codes_x = ["0.02:0.01", "0.04:0.01", "0.06:0.01", "0.11:0.02", "0.11:0.06", "0.12:0.01", "0.12:0.03", "0.12:0.11",
               "0.14:0.01", "0.16:0.01", "0.16:0.11", "0.1:0.01", "0.1:0.02", "0.1:0.03", "0.1:0.04", "0.1:0.05",
               "0.1:0.06", "0.1:0.07", "0.21:0.1", "0.22:0.1", "0.23:0.1", "0.24:0.1", "0.25:0.1", "0.26:0.1",
               "0.27:0.1", "0.2:0.1", "0.2:0.14", "0.41:0.1", "0.42:0.01", "0.42:0.1", "0.42:0.11", "0.43:0.1",
               "0.44:0.01", "0.44:0.1", "0.45:0.1", "0.45:0.22", "0.45:0.23", "0.46:0.01", "0.46:0.1", "0.46:0.11",
               "0.47:0.1", "0.47:0.22", "0.47:0.23", "0.4:0.01", "0.4:0.1", "0.52:0.01", "0.52:0.03", "0.52:0.11",
               "0.53:0.53", "0.54:0.01", "0.56:0.01", "0.56:0.11", "0.57:0.31", "0.57:0.33", "0.5:0.01", "0.5:0.03",
               "0.5:0.12", "0.61:0.1", "0.6:0.1"
               ]
    codes_X = ["0.04:0.04", "0.05:0.02", "0.06:0.05", "0.06:0.06", "0.07:0.07", "0.11:0.03", "0.11:0.04", "0.11:0.05",
               "0.11:0.07", "0.12:0.05", "0.12:0.07", "0.14:0.03", "0.14:0.05", "0.14:0.07", "0.14:0.11", "0.14:0.12",
               "0.14:0.13", "0.14:0.14", "0.16:0.03", "0.16:0.05", "0.16:0.07", "0.16:0.16", "0.17:0.17", "0.21:0.11",
               "0.21:0.12", "0.21:0.14", "0.21:0.16", "0.22:0.11", "0.22:0.14", "0.23:0.11", "0.23:0.12", "0.23:0.14",
               "0.23:0.16", "0.24:0.03", "0.24:0.11", "0.24:0.14", "0.25:0.03", "0.25:0.11", "0.25:0.12", "0.25:0.14",
               "0.25:0.16", "0.26:0.11", "0.26:0.14", "0.27:0.11", "0.27:0.12", "0.27:0.14", "0.27:0.16", "0.2:0.11",
               "0.31:0.15", "0.31:0.16", "0.31:0.17", "0.32:0.13", "0.34:0.13", "0.34:0.31", "0.35:0.33", "0.36:0.13",
               "0.36:0.31", "0.36:0.36", "0.37:0.37", "0.3:0.14", "0.3:0.16", "0.41:0.07", "0.41:0.11", "0.41:0.12",
               "0.41:0.13", "0.41:0.14", "0.41:0.16", "0.41:0.24", "0.41:0.25", "0.41:0.41", "0.42:0.05", "0.42:0.06",
               "0.42:0.4", "0.42:0.42", "0.43:0.07", "0.43:0.11", "0.43:0.12", "0.43:0.14", "0.43:0.16", "0.43:0.24",
               "0.43:0.25", "0.43:0.41", "0.43:0.43", "0.44:0.05", "0.44:0.06", "0.44:0.11", "0.44:0.44", "0.45:0.11",
               "0.45:0.12", "0.45:0.14", "0.45:0.16", "0.45:0.3", "0.45:0.31", "0.45:0.45", "0.46:0.05", "0.46:0.06",
               "0.46:0.44", "0.46:0.46", "0.47:0.11", "0.47:0.12", "0.47:0.14", "0.47:0.16", "0.47:0.45", "0.47:0.47",
               "0.4:0.05", "0.4:0.06", "0.4:0.11", "0.4:0.4", "0.51:0.17", "0.51:0.31", "0.52:0.05", "0.52:0.07",
               "0.52:0.15", "0.52:0.21", "0.52:0.23", "0.52:0.25", "0.52:0.27", "0.52:0.41", "0.52:0.43", "0.52:0.45",
               "0.52:0.47", "0.53:0.31", "0.53:0.33", "0.54:0.03", "0.54:0.05", "0.54:0.07", "0.54:0.11", "0.54:0.15",
               "0.54:0.21", "0.54:0.23", "0.54:0.25", "0.54:0.27", "0.54:0.31", "0.54:0.32", "0.54:0.41", "0.54:0.43",
               "0.54:0.45", "0.54:0.47", "0.55:0.17", "0.55:0.31", "0.55:0.33", "0.56:0.03", "0.56:0.05", "0.56:0.07",
               "0.56:0.15", "0.56:0.21", "0.56:0.23", "0.56:0.25", "0.56:0.27", "0.56:0.41", "0.56:0.43", "0.56:0.45",
               "0.56:0.47", "0.56:0.56", "0.5:0.05", "0.5:0.07", "0.5:0.11", "0.5:0.15", "0.5:0.16", "0.5:0.21",
               "0.5:0.23", "0.5:0.25", "0.5:0.27", "0.5:0.41", "0.5:0.43", "0.5:0.45", "0.5:0.47", "0.61:0.11",
               "0.61:0.12", "0.61:0.13", "0.61:0.14", "0.61:0.16", "0.6:0.11", "0.6:0.14", "0.6:0.6"
               ]
else:
    codes_x=["0.04:0.01", "0.05:0.01", "0.06:0.01", "0.06:0.03", "0.11:0.01", "0.11:0.02", "0.11:0.05", "0.11:0.07", "0.11:0.1", "0.12:0.1", "0.13:0.01", "0.13:0.1", "0.13:0.11", "0.16:0.01", "0.16:0.03", "0.16:0.11", "0.1:0.02", "0.1:0.03", "0.1:0.05", "0.1:0.07", "0.21:0.01", "0.21:0.02", "0.21:0.04", "0.21:0.1", "0.21:0.11", "0.22:0.01", "0.22:0.06", "0.22:0.1", "0.22:0.11", "0.23:0.01", "0.23:0.06", "0.23:0.1", "0.23:0.11", "0.24:0.01", "0.24:0.06", "0.24:0.1", "0.24:0.12", "0.25:0.01", "0.25:0.06", "0.25:0.1", "0.2:0.01", "0.2:0.02", "0.2:0.04", "0.2:0.1", "0.2:0.11", "0.2:0.12", "0.31:0.01", "0.31:0.1", "0.31:0.14", "0.32:0.1", "0.32:0.13", "0.33:0.01", "0.33:0.03", "0.33:0.1", "0.33:0.11", "0.34:0.1", "0.35:0.03", "0.35:0.1", "0.36:0.13", "0.37:0.03", "0.3:0.01", "0.3:0.03", "0.3:0.05", "0.3:0.07", "0.3:0.1", "0.41:0.01", "0.41:0.1", "0.41:0.11", "0.41:0.12", "0.41:0.15", "0.42:0.01", "0.42:0.03", "0.42:0.2", "0.42:0.21", "0.43:0.01", "0.43:0.1", "0.43:0.11", "0.43:0.12", "0.43:0.15", "0.43:0.17", "0.43:0.32", "0.43:0.34", "0.43:0.36", "0.44:0.01", "0.44:0.24", "0.44:0.25", "0.45:0.1", "0.45:0.11", "0.45:0.13", "0.45:0.15", "0.45:0.32", "0.45:0.34", "0.45:0.36", "0.46:0.01", "0.46:0.24", "0.46:0.25", "0.47:0.1", "0.47:0.11", "0.47:0.13", "0.47:0.15", "0.47:0.17", "0.47:0.3", "0.47:0.32", "0.47:0.34", "0.47:0.36", "0.4:0.01", "0.4:0.03", "0.4:0.2", "0.4:0.21", "0.5:0.2", "0.5:0.21"]
    codes_X=["0.03:0.02", "0.04:0.02", "0.04:0.04", "0.05:0.02", "0.05:0.03", "0.05:0.04", "0.06:0.04", "0.06:0.05", "0.06:0.06", "0.07:0.01", "0.07:0.02", "0.07:0.04", "0.07:0.05", "0.07:0.06", "0.07:0.07", "0.11:0.03", "0.12:0.02", "0.12:0.03", "0.12:0.05", "0.12:0.07", "0.12:0.11", "0.13:0.03", "0.13:0.05", "0.13:0.07", "0.13:0.12", "0.14:0.01", "0.14:0.02", "0.14:0.03", "0.14:0.05", "0.14:0.07", "0.14:0.11", "0.14:0.12", "0.14:0.13", "0.14:0.14", "0.15:0.01", "0.15:0.02", "0.15:0.03", "0.15:0.05", "0.15:0.07", "0.15:0.1", "0.15:0.12", "0.15:0.14", "0.15:0.15", "0.16:0.02", "0.16:0.05", "0.16:0.07", "0.16:0.13", "0.16:0.15", "0.16:0.16", "0.17:0.01", "0.17:0.03", "0.17:0.05", "0.17:0.07", "0.17:0.1", "0.17:0.12", "0.17:0.14", "0.17:0.16", "0.17:0.17", "0.21:0.12", "0.21:0.14", "0.21:0.15", "0.21:0.16", "0.22:0.04", "0.23:0.04", "0.24:0.02", "0.24:0.03", "0.24:0.04", "0.24:0.07", "0.24:0.14", "0.24:0.16", "0.25:0.02", "0.25:0.03", "0.25:0.04", "0.25:0.07", "0.25:0.14", "0.26:0.02", "0.26:0.04", "0.26:0.06", "0.26:0.26", "0.27:0.02", "0.27:0.04", "0.27:0.06", "0.27:0.26", "0.27:0.27", "0.2:0.14", "0.2:0.15", "0.2:0.16", "0.31:0.03", "0.31:0.05", "0.31:0.07", "0.31:0.11", "0.31:0.15", "0.31:0.16", "0.31:0.17", "0.32:0.01", "0.32:0.03", "0.32:0.05", "0.32:0.07", "0.32:0.11", "0.32:0.15", "0.32:0.17", "0.32:0.31", "0.33:0.05", "0.33:0.07", "0.34:0.01", "0.34:0.03", "0.34:0.05", "0.34:0.07", "0.34:0.13", "0.34:0.14", "0.34:0.15", "0.34:0.16", "0.34:0.17", "0.34:0.31", "0.35:0.01", "0.35:0.05", "0.35:0.07", "0.35:0.14", "0.35:0.35", "0.36:0.01", "0.36:0.03", "0.36:0.05", "0.36:0.07", "0.36:0.15", "0.36:0.17", "0.36:0.31", "0.36:0.32", "0.36:0.35", "0.36:0.36", "0.37:0.01", "0.37:0.05", "0.37:0.07", "0.37:0.33", "0.37:0.37", "0.3:0.11", "0.3:0.14", "0.3:0.16", "0.41:0.02", "0.41:0.04", "0.41:0.05", "0.41:0.06", "0.41:0.07", "0.41:0.13", "0.41:0.14", "0.41:0.16", "0.41:0.17", "0.41:0.24", "0.41:0.25", "0.41:0.3", "0.41:0.31", "0.41:0.32", "0.41:0.33", "0.41:0.34", "0.41:0.35", "0.41:0.36", "0.41:0.37", "0.41:0.4", "0.41:0.41", "0.42:0.04", "0.42:0.05", "0.42:0.06", "0.42:0.07", "0.42:0.22", "0.42:0.23", "0.42:0.24", "0.42:0.25", "0.42:0.26", "0.42:0.27", "0.42:0.4", "0.42:0.41", "0.42:0.42", "0.43:0.02", "0.43:0.04", "0.43:0.05", "0.43:0.06", "0.43:0.07", "0.43:0.14", "0.43:0.16", "0.43:0.24", "0.43:0.25", "0.43:0.31", "0.43:0.33", "0.43:0.35", "0.43:0.37", "0.43:0.4", "0.43:0.41", "0.43:0.42", "0.43:0.43", "0.44:0.04", "0.44:0.05", "0.44:0.06", "0.44:0.07", "0.44:0.22", "0.44:0.23", "0.44:0.26", "0.44:0.27", "0.44:0.4", "0.44:0.42", "0.44:0.44", "0.45:0.01", "0.45:0.02", "0.45:0.04", "0.45:0.05", "0.45:0.06", "0.45:0.07", "0.45:0.12", "0.45:0.14", "0.45:0.16", "0.45:0.17", "0.45:0.22", "0.45:0.23", "0.45:0.24", "0.45:0.25", "0.45:0.31", "0.45:0.33", "0.45:0.35", "0.45:0.37", "0.45:0.4", "0.45:0.42", "0.45:0.44", "0.45:0.45", "0.46:0.04", "0.46:0.05", "0.46:0.06", "0.46:0.07", "0.46:0.22", "0.46:0.23", "0.46:0.26", "0.46:0.27", "0.46:0.4", "0.46:0.42", "0.46:0.44", "0.46:0.45", "0.46:0.46", "0.47:0.01", "0.47:0.02", "0.47:0.04", "0.47:0.05", "0.47:0.06", "0.47:0.07", "0.47:0.12", "0.47:0.14", "0.47:0.16", "0.47:0.22", "0.47:0.23", "0.47:0.24", "0.47:0.25", "0.47:0.31", "0.47:0.33", "0.47:0.35", "0.47:0.37", "0.47:0.4", "0.47:0.42", "0.47:0.44", "0.47:0.45", "0.47:0.46", "0.47:0.47", "0.4:0.04", "0.4:0.05", "0.4:0.06", "0.4:0.07", "0.4:0.22", "0.4:0.23", "0.4:0.24", "0.4:0.25", "0.4:0.26", "0.4:0.27", "0.4:0.4", "0.5:0.01", "0.5:0.02", "0.5:0.03", "0.5:0.05", "0.5:0.07", "0.5:0.11", "0.5:0.12", "0.5:0.13", "0.5:0.14", "0.5:0.15", "0.5:0.16", "0.5:0.17", "0.5:0.41", "0.5:0.43"]
recorded_game_type = dict.fromkeys(codes_x, "x") | dict.fromkeys(codes_X, "X")


start_time = time.time()
game_start_time = time.time()

for index, ((index_L, index_R), game) in enumerate(partizan_octal_game.enum_games(reverse=reverse,
                                                                                  terminal_sg=TERMINAL_SG)):

    # for index, ((index_L, index_R), game) in enumerate(misere_octal_game.enum_games(reverse=reverse, terminal_sg=1)):

    game: partizan_octal_game
    # game: misere_octal_game

    PRINT_KEY_ONLY = False

    # 跳过平凡情形（否则自动机相关运算会卡bug）
    if bidim(game.code_L) == 0 or bidim(game.code_R) == 0:
        image_renew(resolvable_image, (index_L, index_R), " ")
        recorded_game_type[game.code] = " "
        continue

    # 跳过已记录的情形
    if game.code in recorded_game_type:
        continue

    game_start_time = time.time()
    for _ in range(1):

        game_type = "?"

        write("=" * 50, key=True)
        game.write_describe()

        try:
            P_nfa, N_nfa = game.get_sg_nfa(test_suffixes=test_suffixes, max_state_num=MAX_STATE_NUM)
        except OverflowError:
            P_nfa, N_nfa = None, None

        # sg_list = [game.get_sg((heap,)) for heap in range(1, 100) if (heap,) in game.recorded_sg]
        # write(f"Heap OC: {", ".join(sg_str(sg) for sg in sg_list)},...", key=True)
        # write(f"  Heap period: {(heap_per:=detect_period(sg_list))}", key=True)

        # 自动机未找到
        if P_nfa is None:
            game_type = "X"
            # write(f"\033[31mOutcome-DFA state num overflowed (>{MAX_STATE_NUM})!\033[0m ", key=True)

            image_renew(resolvable_image, (index_L, index_R), game_type)
            recorded_game_type[game.code] = game_type
            continue

        # 清空SG值记录，为自动机的计算腾出内存
        game.recorded_sg = {}

        # 各种状态的计数
        class_nums = (len([state for state in P_nfa.final_states if state[:1] == "L"]),
                      len([state for state in N_nfa.final_states if state[:1] == "L"]),
                      len([state for state in P_nfa.final_states if state[:1] == "R"]),
                      len([state for state in N_nfa.final_states if state[:1] == "R"]))

        # 展示找到的自动机
        write("-" * 50)
        # write(N_nfa)

        irred_prefixes_P_L, irred_prefixes_P_R = [], []
        irred_prefixes_N_L, irred_prefixes_N_R = [], []
        for state in N_nfa.states:

            if len(state) <= 1:
                continue

            if state[-1:] == "x":
                if state[:1] == "L":
                    if state in N_nfa.final_states:
                        irred_prefixes_N_L.append(state)
                    else:
                        irred_prefixes_P_L.append(state)
                else:
                    if state in N_nfa.final_states:
                        irred_prefixes_N_R.append(state)
                    else:
                        irred_prefixes_P_R.append(state)

        write(f"Irreducible prefixes "
              f"({len(irred_prefixes_P_L)}+{len(irred_prefixes_N_L)}+{len(irred_prefixes_P_R)}+{len(irred_prefixes_N_R)}"
              f"={len(irred_prefixes_N_L) + len(irred_prefixes_P_L) + len(irred_prefixes_N_R) + len(irred_prefixes_P_R)}"
              f" for P_L+N_L+P_R+N_R):")
        write(f"  P_L: {", ".join(f"{prefix_str(prefix)}" for prefix in irred_prefixes_P_L)}")
        write(f"  N_L: {", ".join(f"{prefix_str(prefix)}" for prefix in irred_prefixes_N_L)}")
        write(f"  P_R: {", ".join(f"{prefix_str(prefix)}" for prefix in irred_prefixes_P_R)}")
        write(f"  N_R: {", ".join(f"{prefix_str(prefix)}" for prefix in irred_prefixes_N_R)}")

        reductions_L, reductions_R = [], []
        for state, chara, next_state in N_nfa.enum_trans(sort=True):

            if len(state) <= 1 or len(next_state) <= 1:
                continue

            if not game.prefix_equiv(state + chara, next_state):
                if state[:1] == "L":
                    reductions_L.append((state + chara, next_state))
                else:
                    reductions_R.append((state + chara, next_state))

        write(f"Prefix reductions "
              f"({len(reductions_L)}+{len(reductions_R)}={len(reductions_L) + len(reductions_R)} for L+R):")
        write(f"  L: {", ".join(f"{prefix_str(prefix)}->{prefix_str(next_prefix)}"
                                for prefix, next_prefix in reductions_L)}")
        write(f"  R: {", ".join(f"{prefix_str(prefix)}->{prefix_str(next_prefix)}"
                                for prefix, next_prefix in reductions_R)}")

        try:
            next_P_nfa = (P_nfa.comp_rewrite(("L", "R")).comp_rewrite(game.to_rewrite("L"))
                          | P_nfa.comp_rewrite(("R", "L")).comp_rewrite(game.to_rewrite("R")))
            next_P_nfa.name = f"next({P_nfa.name})"

            # write("-" * 50)
            # write(next_P_nfa)

            prev_P_nfa = (P_nfa.comp_rewrite(("L", "R")).comp_rewrite(game.to_rewrite("R", reverse=True))
                          | P_nfa.comp_rewrite(("R", "L")).comp_rewrite(game.to_rewrite("L", reverse=True)))
            prev_P_nfa.name = f"prev({P_nfa.name})"

        # 自动机状态数溢出
        except OverflowError:
            game_type = "X"

            write(f"\033[31mPrev/Next-DFA state number overflowed (>{50000})!\033[0m ", key=True)

            image_renew(resolvable_image, (index_L, index_R), game_type)
            recorded_game_type[game.code] = game_type
            continue

        # write("-" * 50)
        # write(prev_P_nfa, key=True)

        # next_P_nfa = P_nfa.comp_rewrite(game.to_rewrite())
        # next_P_nfa.name = f"next({P_nfa.name})"
        #
        # # write("-" * 50)
        # # write(next_P_nfa)
        #
        # prev_P_nfa = P_nfa.comp_rewrite(game.to_rewrite(reverse=True))
        # prev_P_nfa.name = f"prev({P_nfa.name})"
        #
        # # write("-" * 50)
        # # write(prev_P_nfa, key=True)

        write("-" * 50)
        write(f"Final/total state nums:")
        write(f"  P: {len(P_nfa.final_states)}/{len(P_nfa.states)}")
        write(f"  N: {len(N_nfa.final_states)}/{len(N_nfa.states)}")
        write(f"  prev(P): {len(prev_P_nfa.final_states)}/{len(prev_P_nfa.states)}")
        write(f"  next(P): {len(next_P_nfa.final_states)}/{len(next_P_nfa.states)}")

        term_nfa = game.get_terminals_nfa()

        # 需要满足的三个条件
        conds = {"T": None, "0": None, "1": None}
        cond_texts = {"T": f"T <= {"P" if game.terminal_sg == 0 else "N"}",
                      "0": "next(P) <= N",
                      "1": f"N{"" if game.terminal_sg == 0 else "\\T"} <= prev(P)"}

        write("-" * 50)
        write(f"Conditions:", key=True)

        for cond_code in "T01":

            cond = None
            try:
                # 条件T：终局一定是P局面（misere规则则一定是N局面）
                if cond_code == "T":
                    cond = (term_nfa <= P_nfa) if game.terminal_sg == 0 else (term_nfa <= N_nfa)

                # 条件0： P局面可达的一定是N局面，next(P) <= N
                elif cond_code == "0":
                    cond = next_P_nfa <= N_nfa

                elif cond_code == "1":
                    cond = (N_nfa if game.terminal_sg == 0 else (N_nfa - term_nfa)) <= prev_P_nfa

            except OverflowError:
                cond = None

            conds[cond_code] = cond

            write(f"  {cond_texts[cond_code]}: "
                  f"{"\033[32mTrue\033[0m" if cond else "\033[31mFalse\033[0m"}", key=True)

            if not cond:
                break

        if not all(conds.values()):
            game_type = "x"

            write("\033[31mFailed to prove!\033[0m "
                  f"({len(N_nfa.states)} states)", key=True)

        else:
            game_type = "V"

            write("\033[32mSucceed to prove!\033[0m "
                  f"(P_L,N_L,P_R,N_R-class num={",".join(str(num) for num in class_nums)}, "
                  f"sum class num={sum(class_nums)}, "
                  f"state num={len(N_nfa.states)})", key=True)

        image_renew(resolvable_image, (index_L, index_R), game_type)
        recorded_game_type[game.code] = game_type

        # 记录当前nfa
        if game_type=="V":
            recorded = False
            for old_code, old_N_nfa in recorded_N_nfa.items():
                if recorded_class_nums[old_code] == class_nums and old_N_nfa.trans_map == N_nfa.trans_map:
                    N_nfa_equiv_class[old_code].append(game.code)
                    recorded = True
                    write(f"  Outcomes equal to {old_code}", key=True)
                    break

            if not recorded:
                recorded_N_nfa[game.code] = N_nfa.copy()
                recorded_class_nums[game.code] = class_nums
                N_nfa_equiv_class[game.code] = [game.code]
                # write(f"New equivalent class recorded")

    PRINT_KEY_ONLY = True

    write("=" * 50, output_path=CLASSES_OUTPUT_PATH, cover=True)
    write(f"DFA equivalent classes:", output_path=CLASSES_OUTPUT_PATH)
    for i, code in enumerate(sorted(N_nfa_equiv_class.keys())):
        equiv_class = N_nfa_equiv_class[code]
        write(f"  {'"' + code + '": {'}"
              f"{", ".join('"' + equiv_code + '"' for equiv_code in equiv_class)}"
              f"{'}, '}"
              f" # {len(equiv_class)} DFAs, "
              f"P_L,N_L,P_R,N_R-class num={",".join(str(num) for num in recorded_class_nums[code])}, "
              f"sum class num={sum(recorded_class_nums[code])}, "
              f"state num={len(recorded_N_nfa[code].states)}", output_path=CLASSES_OUTPUT_PATH)

    write("-" * 50, output_path=CLASSES_OUTPUT_PATH)
    write(f"Unsolvable games:", output_path=CLASSES_OUTPUT_PATH)
    for game_type in "xX":
        game_codes = sorted(old_code for old_code, old_game_type in recorded_game_type.items()
                            if old_game_type == game_type)
        write(f"  {GAME_TYPE_TEXT["resolvable"][game_type]} ({len(game_codes)} for total): "
              f"{", ".join('"' + game_code + '"' for game_code in game_codes)}", output_path=CLASSES_OUTPUT_PATH)

    PRINT_KEY_ONLY = False

    used_time = time.time() - start_time
    game_used_time = time.time() - game_start_time
    write(f"  ({round(game_used_time / 60, 4)}min used, {round(used_time / 60, 4)}min for total)")
    print(f"  (about {round(used_time / (index + 1) * (2628 - (index + 1)) / 60, 4)}min remained)")

# OUTPUT_PATH = "result\\partizan_octal\\nfa_classes.txt"
# """输出txt文件的地址"""
#
# write(f"Date: 2026/7/6", cover=True, key=True)
#
# write("=" * 50)
# write(f"NFA equivalent classes:", key=True)
# for i, code in enumerate(sorted(N_nfa_equiv_class.keys())):
#     equiv_class = N_nfa_equiv_class[code]
#     write(f"  #{i + 1} ({len(recorded_N_nfa[code].states)} states, "
#           f"{recorded_class_num[code][0]}/{recorded_class_num[code][1]} N-classes): "
#           f"{", ".join('"' + equiv_code + '"' for equiv_code in equiv_class)}", key=True)
#
# write("-" * 50)
# write(f"Unsolvable games:", key=True)
# for game_type in "xX":
#     game_codes = sorted(old_code for old_code, old_game_type in recorded_game_type.items()
#                         if old_game_type == game_type)
#     write(f"  {GAME_TYPE_TEXT["resolvable"][game_type]} ({len(game_codes)} for total): "
#           f"{", ".join('"' + game_code + '"' for game_code in game_codes)}", key=True)
