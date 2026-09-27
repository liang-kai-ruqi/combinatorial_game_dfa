"""
2026/6/17
2026/7/19 修改
该包提供自动机理论中常用的结构与函数。

基础结构的格式：
    字符（状态）：单个字符的str，或str|int组成的元组(str|int,...)。
    词：若字符为str格式，则词为字符拼接成的str；否则为字符组成的元组((str|int,...),...)。字符的拼接用+，长度用len()。
    字符（状态）表：字符的列表list。
    映射：(状态, 字符)到下一状态（集合）的字典dict。

关于格式兼容：
    1. 词参数的格式（str或tuple）由自动机的字符格式chara_type决定，函数会自动转换，
       所以 str 格式（如"01"）与 tuple 格式（如("0","1")）的词都可以传给同一个函数；
    2. 状态可以是int|str|tuple格式，同一个自动机内要求统一（state_type）；
    3. enum_trans枚举的每个转变都是二元组 ((状态, 字符), 下一状态)，与trans_map.items()的形式一致；
    4. dfa是nfa的子类：初始状态唯一，每个(状态,字符)最多有一个下一状态（内部仍以单元素set存储，
       以复用nfa的全部函数）。nfa与dfa可以混合运算，混合运算的结果是nfa，
       而两个dfa的交、并、补、差运算的结果仍是dfa。
"""
import time

# USED_NAME = []

from collections import deque
from ACG import *

# MAX_STATE_NUM = 50000
MAX_STATE_NUM = 100000

OPER_SYMBS = {"+", "-", "*", "/", "%", "@", "&", "|"}
"""特殊运算符号"""

EXPR_SYMBS = set("()*+~|&@")
"""表达式中具有特殊含义的符号"""


"""↓↓格式的判断与转换：↓↓"""


def is_chara(item):
    """判断item是否为字符格式：单个字符的str，或str|int组成的元组"""
    if type(item) is str:
        return len(item) == 1
    elif type(item) is tuple:
        return all((type(ch) is str and len(ch) == 1) or type(ch) is int for ch in item)
    else:
        return False


def is_word(item):
    """判断item是否为词格式：str，或由字符组成的元组"""
    if type(item) is str:
        return True
    elif type(item) is tuple:
        return all(is_chara(ch) for ch in item)
    else:
        return False


def is_rewrite(item):
    """判断item是否为一个重写规则：(原词, 新词) 或 (原词, 新词, 定位方式)"""
    if type(item) is not tuple and type(item) is not list:
        return False
    if not 2 <= len(item) <= 3:
        return False
    return is_word(item[0]) and is_word(item[1])


def chara_to_str(chara):
    """把字符转换成str格式"""
    if type(chara) is str:
        return chara
    elif type(chara) is tuple:
        return "".join(str(ch) for ch in chara)
    else:
        return str(chara)


def chara_to_tuple(chara):
    """把字符转换成tuple格式"""
    if type(chara) is tuple:
        return chara
    elif type(chara) is str:
        return tuple(chara)
    else:
        return (chara,)


def word_to_str(word):
    """把词转换成str格式"""
    if type(word) is str:
        return word
    elif type(word) is tuple:
        return "".join(chara_to_str(chara) for chara in word)
    else:
        return str(word)


def word_to_tuple(word):
    """把词转换成tuple格式"""
    if type(word) is tuple:
        return word
    elif type(word) is str:
        return tuple(word)
    else:
        return (word,)


def convert_chara(chara, to_type):
    """把字符转换成指定格式"""
    return chara_to_str(chara) if to_type is str else chara_to_tuple(chara)


def convert_word(word, to_type):
    """把词转换成指定格式"""
    return word_to_str(word) if to_type is str else word_to_tuple(word)


def segment_word(word, charas):
    """把str格式的词按字符表charas切分成tuple格式的词"""
    word = word_to_str(word)

    chara_strs = [(chara_to_str(chara), chara) for chara in charas]
    chara_strs = [(chara_str_, chara) for chara_str_, chara in chara_strs if chara_str_]
    chara_strs.sort(key=lambda pair: -len(pair[0]))

    # 所有字符都是单字符时直接切分
    if all(len(chara_str_) == 1 for chara_str_, chara in chara_strs):
        chara_map = {chara_str_: chara for chara_str_, chara in chara_strs}
        return tuple(chara_map.get(ch, ch) for ch in word)

    # 否则按最长匹配切分
    new_word = ()
    i = 0
    while i < len(word):
        for chara_str_, chara in chara_strs:
            if word.startswith(chara_str_, i):
                new_word += (chara,)
                i += len(chara_str_)
                break
        else:
            new_word += (word[i],)
            i += 1
    return new_word


def to_word_set(words):
    """把输入统一成词的集合set。
    约定：
        str视为一个词（""是只含空词的语言）；
        list/set/frozenset视为多个词的集合（[]与set()是空语言）；
        元组中各元素都是字符时视为一个词（()是只含空词的语言），否则视为多个词的集合。
    """
    if words is None:
        return set()
    if type(words) is str:
        return {words}
    if type(words) is tuple:
        if len(words) == 0:
            return {()}
        if all(is_chara(item) for item in words):
            return {words}
        return set(words)
    if type(words) is list or type(words) is set or type(words) is frozenset:
        return set(words)
    return {words}


def to_state_set(states):
    """把状态输入统一成集合set（单个状态可以是int|str|tuple，即元组视为一个状态）"""
    if type(states) is set or type(states) is frozenset:
        return set(states)
    if type(states) is list:
        return set(states)
    if type(states) is dict:  # 兼容{状态: 标签}格式的终止状态映射
        return set(states)
    return {states}


def sorted_items(items):
    """尽可能自然地排序，元素之间无法比较时退化为按字符串排序"""
    items = list(items)
    try:
        return sorted(items)
    except TypeError:
        return sorted(items, key=lambda item: (str(type(item)), str(item)))


def make_state(old_state=None, state_type=int, avoid_states=None):
    """构造一个state_type格式的新状态：尽量以old_state为基底，且不在avoid_states中"""
    if avoid_states is None:
        avoid_states = set()

    # 状态为整数格式，新状态取状态中未出现的最小自然数
    if state_type is int:
        base = old_state if type(old_state) is int else None
        new_state = 0 if base is None else base
        while new_state in avoid_states:
            new_state += 1
        return new_state

    # 状态为tuple格式，新状态由给旧状态后加一个保证状态不重复的最小自然数得到
    elif state_type is tuple:
        base = old_state if type(old_state) is tuple else ()
        if base not in avoid_states:
            return base
        i = 0
        new_state = base + (i,)
        while new_state in avoid_states:
            i += 1
            new_state = base + (i,)
        return new_state

    # 状态为str格式，新状态由给旧状态添加下标得到，下标为保证状态不重复的最小正整数
    elif state_type is str:
        if old_state is None:
            base = "s"
        elif type(old_state) is str:
            base = old_state
        else:
            base = str(old_state)

        if base not in avoid_states:
            return base
        i = 0
        new_state = f"{base}_{i}"
        while new_state in avoid_states:
            i += 1
            new_state = f"{base}_{i}"
        return new_state

    else:
        raise NotImplementedError(f"不支持的状态格式：{state_type}")


def word_str(word, bucket=("", "")):
    """词的打印时的字符串。"""
    buc, ket = bucket
    if type(word) is str:
        return f"{buc}{deblank(word)}{ket}"
    elif type(word) is tuple:
        return f"{buc}{','.join(deblank(chara) for chara in word)}{ket}"
    else:
        return f"{buc}{deblank(word)}{ket}"


def chara_str(chara):
    """字符的打印时的字符串。"""
    return deblank(chara)


def align_fa(fa1, fa2):
    """统一两个自动机的字符格式与字符表（字符表取并集），返回两个副本。"""

    type1, type2 = fa1.chara_type, fa2.chara_type

    if type1 is type2:
        new_fa1 = fa1.copy(name=fa1.name)
        new_fa2 = fa2.copy(name=fa2.name)
    else:
        # 优先统一为str格式，出现冲突时再统一为tuple格式
        try:
            if type1 is str:
                new_fa1 = fa1.copy(name=fa1.name)
                new_fa2 = fa2.convert_charas(str)
            else:
                new_fa1 = fa1.convert_charas(str)
                new_fa2 = fa2.copy(name=fa2.name)
        except (ValueError, TypeError):
            new_fa1 = fa1.convert_charas(tuple)
            new_fa2 = fa2.convert_charas(tuple)

    charas = list(new_fa1.charas)
    charas += [chara for chara in new_fa2.charas if chara not in charas]
    new_fa1.charas = charas
    new_fa2.charas = charas

    return new_fa1, new_fa2


def state_prime(state, avoid_states=None, state_type=None):
    """给状态加上撇号，要求避开avoid_states中的状态"""
    if state_type is None:
        state_type = type(state) if state is not None else str
    return make_state(state, state_type, avoid_states)


# read_expr在文件末尾给出（与nfa.from_expr等价）


def any_item(S):
    """从集合或者列表中任取一项"""
    for s in S:
        return s


class nfa:
    """
    非确定性有限状态自动机。由以下结构组成：
      字符表：字符/单元组组成的列表。
      状态表：任意可哈希元素组成的列表。
      转变（超）映射：形如 (p, a) -> {q1, ...} 的字典。
      初始状态：其中任意个状态。
      终止状态：其中任意个状态。

         p0·a0,a1,a2·Q -next-> p1·a1,a2·Q -next-> p2·a2·Q -next-> p3·Q -final_0-> tag
    <==> p0·a0,a1,a2·Q -final-> tag
    """

    charas: list
    states: list
    init_states: set
    final_states: set
    trans_map: dict[any: set]
    name: str
    max_state_num: int

    def __init__(self, trans_map: dict | tuple = None, charas: str | list = None, states: str | list = None,
                 init_states: str | set = None, final_states: str | set = None, name="A",
                 max_state_num=MAX_STATE_NUM):

        self.trans_map = self.normalize_trans_map(trans_map)
        """转变函数（超映射）。表示为dict[(状态,字符):set(状态)]格式。"""

        if charas is None:
            self.charas = sorted_items({chara for (state, chara), next_state in self.enum_trans()})
            """字符表。默认为转变中包含的全部字符。"""
        else:
            self.charas = list(charas)

        if states is None:
            all_states = set()
            for (state, chara), next_state in self.enum_trans():
                all_states.add(state)
                all_states.add(next_state)
            self.states = sorted_items(all_states)
            """状态表，不能为空。默认为转变中包含的全部状态。"""
        else:
            self.states = list(states)

        # 状态表为空则添加一个死状态
        if len(self.states) == 0:
            self.states.append(0)

        if init_states is None:
            self.init_states = {self.states[0]}
            """初始状态的集合，格式为set。默认为状态表首个状态。"""
        else:
            self.init_states = to_state_set(init_states)

        if final_states is None:
            self.final_states = {self.states[-1]}
            """终止状态的集合，格式为set。默认为状态表末个状态。"""
        else:
            self.final_states = to_state_set(final_states)

        self.name = name
        """nfa的名称"""

        self.max_state_num = max_state_num
        """状态数上限"""

        self._state_set_cache = None
        """状态集合的缓存，用于加速add_states"""

        self._chara_set_cache = None
        """字符集合的缓存，用于加速to_local_word"""

        self._int_state_hint = None
        """int格式状态下新状态的计数提示，用于加速add_states"""

    '''↓↓格式相关的内部函数：↓↓'''

    @staticmethod
    def normalize_trans_map(trans_map):
        """把转变映射统一成{(状态,字符):set(下一状态)}的格式。
        trans_map既可以是dict，也可以是由((状态,字符),下一状态)组成的可迭代对象。
        注意：作为下一状态的元组会被视为单个状态（多个状态请用set/list表示）。
        """
        if trans_map is None:
            return {}

        if type(trans_map) is dict:
            items = trans_map.items()
        else:
            items = trans_map

        new_trans_map = {}
        for key, value in items:
            next_states = nfa.normalize_next_states(value)
            if key in new_trans_map:
                new_trans_map[key] |= next_states
            else:
                new_trans_map[key] = set(next_states)

        return new_trans_map

    @staticmethod
    def normalize_next_states(value):
        """把下一状态统一成set"""
        if type(value) is set or type(value) is frozenset or type(value) is list:
            return set(value)
        if hasattr(value, "__iter__") and not isinstance(value, (str, bytes, tuple)):
            return set(value)
        return {value}

    @property
    def state_type(self):
        """状态的格式，要求是统一的"""
        return type(self.states[0]) if self.states else int

    @property
    def chara_type(self):
        """字符的格式（str或tuple）：字符都是str时为str，只要有一个是元组则为tuple"""
        charas = self.charas if self.charas else [chara for (state, chara) in self.trans_map]
        return str if all(type(chara) is str for chara in charas) else tuple

    @property
    def word_type(self):
        """词的格式（str或tuple）。
        词是字符串的拼接，或字符组成的元组：字符为str格式时词为str，否则词为tuple。
        """
        return self.chara_type

    @property
    def empty_word(self):
        """空词"""
        return "" if self.word_type is str else ()

    def to_local_word(self, word):
        """把词转换成该自动机的词格式。
        str格式的词转成tuple格式时，会按本自动机的字符表切分。
        """
        if self.word_type is str:
            if type(word) is str:
                return word
            return word_to_str(word)
        else:
            # 已经是本自动机的字符组成的元组
            if type(word) is tuple and all(chara in self._chara_set for chara in word):
                return word
            return self.segment_word(word)

    def segment_word(self, word):
        """把str格式的词按本自动机的字符表切分成tuple格式的词"""
        return segment_word(word, self.charas)

    def convert_charas(self, to_type=str):
        """把字符表和转变中的字符统一转换成str或tuple格式，返回新的自动机。
        str格式的字符"ab"与tuple格式的字符("a","b")是同一个字符的两种写法。
        """
        if self.chara_type is to_type:
            return self.copy()

        new_charas = [convert_chara(chara, to_type) for chara in self.charas]
        if len(set(new_charas)) != len(new_charas):
            raise ValueError(f"字符格式转换后出现重复：{new_charas}")

        new_trans_map = {}
        for (state, chara), next_states in self.trans_map.items():
            key = (state, convert_chara(chara, to_type))
            if key in new_trans_map:
                raise ValueError(f"字符格式转换后出现冲突：{key}")
            new_trans_map[key] = set(next_states)

        return type(self)(trans_map=new_trans_map,
                          charas=new_charas,
                          states=list(self.states),
                          init_states=set(self.init_states),
                          final_states=set(self.final_states),
                          name=self.name,
                          max_state_num=self.max_state_num)

    def copy(self, name=None):
        """复制"""

        return type(self)(trans_map={symb: next_symbs.copy() for symb, next_symbs in self.trans_map.items()},
                          states=self.states.copy(),
                          charas=self.charas.copy(),
                          init_states=self.init_states.copy(),
                          final_states=self.final_states.copy(),
                          name=self.name if name is None else name,
                          max_state_num=self.max_state_num)

    def to_nfa(self):
        """转换成等价的nfa（若已经是nfa则返回自身）"""
        if type(self) is nfa:
            return self
        return nfa(trans_map={symb: next_symbs.copy() for symb, next_symbs in self.trans_map.items()},
                   states=self.states.copy(),
                   charas=self.charas.copy(),
                   init_states=self.init_states.copy(),
                   final_states=self.final_states.copy(),
                   name=self.name,
                   max_state_num=self.max_state_num)

    def to_dfa(self, complete=False):
        """转换成等价的dfa（若已经是dfa则返回自身副本）"""
        if isinstance(self, dfa):
            new_dfa = self.copy()
            return new_dfa.complete() if complete else new_dfa
        return self.determinize(to_type="dfa", complete=complete)

    def fit_type(self, prefer_dfa=False):
        """返回结构与其类型相符的自动机：结构已非确定时退化为nfa；prefer_dfa且结构确定时可升级为dfa。"""
        if self.is_deterministic():
            if isinstance(self, dfa):
                return self
            elif prefer_dfa:
                return dfa(trans_map={symb: next_symbs.copy() for symb, next_symbs in self.trans_map.items()},
                           states=self.states.copy(),
                           charas=self.charas.copy(),
                           init_states=self.init_states.copy(),
                           final_states=self.final_states.copy(),
                           name=self.name,
                           max_state_num=self.max_state_num)
            else:
                return self

        if isinstance(self, dfa):
            return self.to_nfa()
        return self

    def state_type_uniformize(self, to_type=int):
        """统一状态格式，返回新的自动机"""

        state_rename = {}
        used_states = set()

        for state in self.states:

            if to_type is int:
                new_state = len(state_rename)

            elif to_type is str:
                base = state if type(state) is str else str(state)
                new_state = make_state(base, str, used_states)

            elif to_type is tuple:
                base = state if type(state) is tuple else (state,)
                new_state = make_state(base, tuple, used_states)

            else:
                raise NotImplementedError(f"不支持的状态格式：{to_type}")

            state_rename[state] = new_state
            used_states.add(new_state)
        new_fa = type(self)(trans_map={},
                            charas=self.charas.copy(),
                            states=list(state_rename.values()),
                            init_states={state_rename[init_state] for init_state in self.init_states
                                         if init_state in state_rename},
                            final_states={state_rename[final_state] for final_state in self.final_states
                                          if final_state in state_rename},
                            name=self.name,
                            max_state_num=self.max_state_num)

        for (state, chara), next_state in self.enum_trans():
            if state in state_rename and next_state in state_rename:
                new_fa.add_trans((state_rename[state], chara), state_rename[next_state])

        return new_fa

    '''↓↓内部的属性：↓↓'''

    def trans_map_str(self, max_len=None):
        """给出表示转变的字符串"""
        text = ""
        for i, ((state, chara), next_state) in enumerate(self.enum_trans()):
            if i > 0:
                text += ", "
            text += f"{chara_str(state)}·{chara_str(chara)}->{chara_str(next_state)}"

            if max_len is not None and i + 1 == max_len:
                text += ",..."
                break

        return text

    '''↓↓打印与显示：↓↓'''

    def describe(self, max_len=None, word_max_len=None):
        """打印时的文本"""

        text = f"Finite state automaton {self.name}:\n"
        text += (f"  states (size={len(self.states)}, type={self.state_type.__name__}): \n"
                 f"    {", ".join(deblank(state) for state in self.states[:max_len])}\n"

                 f"  charas (size={len(self.charas)}): "
                 f"{", ".join(deblank(chara) for chara in self.charas[:max_len])},\n"

                 f"  trans_map (size={sum(len(next_symbs) for symb, next_symbs in self.trans_map.items())}, "
                 f"{"" if self.is_deterministic() else "non-"}deterministic): \n"
                 f"    {self.trans_map_str(max_len)}\n"

                 f"  init_states (size={len(self.init_states)}): "
                 f"{", ".join(deblank(state) for state in self.states
                              if state in self.init_states)},\n"

                 f"  final_states (size={len(self.final_states)}): "
                 f"{", ".join(deblank(state) for state in self.states
                              if state in self.final_states)},\n")

        # 展示接受的词
        if word_max_len:
            word_num = max_len if max_len else 100
            words = list(self.enum_words(range(word_max_len + 1), max_num=word_num))
            text += (f"  Examples of words (len<={word_max_len}, num<={word_num}):\n"
                     f"    {", ".join(word_str(word) for word in words)},...")

        return text

    def __str__(self):
        """默认的字符串表示"""
        return self.describe(100, 8)

    def show(self, image_size=(1200, 800), back_color=(0, 0, 0), font_size=20):
        """显示图片"""
        """这个功能太复杂，且用处不大，暂时不用"""

        image = Image.new("RGB", image_size, back_color)

        # 各个状态的正，反向距离
        forward_dists = self.distance_from(self.init_states)
        # backward_dists = self.distance_from(self.final_states, backward=True)
        #
        # max_dist = max(set(forward_dists.values()) | set(backward_dists.values()))
        max_dist = max(set(forward_dists.values()))

        state_xy_dict = {}

        for i, state in enumerate(self.states):
            state_y = 50 + (image_size[1] - 100) * i / len(self.states)

            # ratio = (forward_dists.get(state, max_dist + 1)
            #          / (forward_dists.get(state, max_dist + 1) + backward_dists.get(state, max_dist + 1)))

            ratio = forward_dists.get(state, max_dist + 1) / (max_dist + 1)

            state_x = 50 + (image_size[0] - 100) * ratio

            state_xy_dict[state] = (state_x, state_y)

            draw_text(image, (state_x, state_y), (255, 255, 255), str(state), font_size)

        for (state, chara), next_state in self.enum_trans():

            if state != next_state:
                pos = state_xy_dict[state] + state_xy_dict[next_state] + (font_size / 2, font_size / 2)
                draw_arrow(image, pos, (255, 255, 255), tag=chara_str(chara), tag_size=font_size)

            # 转入原状态，绘制指向自身的箭头
            else:
                state_x, state_y = state_xy_dict[state]
                draw = ImageDraw.Draw(image)
                draw.arc((state_x, state_y, state_x + 40, state_y + 40), -90, 180, (255, 255, 255), 2)
                draw_text(image, (state_x + 20, state_y + 20), (255, 255, 255), chara_str(chara), font_size)
                draw_arrow(image, (state_x + 20, state_y, state_x + 19, state_y), (255, 255, 255),
                           tag=chara_str(chara), tag_size=font_size)

        image.show()

    '''↓↓关于确定性的属性和方法：↓↓'''

    def is_deterministic(self, strict=False):
        """是否为确定性的。
        如果strict==False，则仅要求 初始状态不多于一个 且 (状态, 字符) 对应的下一状态数不大于1，
        无输出不破坏确定性（将被视为转入一个死状态）。
        如果strict==True，还要求每个(状态, 字符)都有恰好一个下一状态（即转移函数完整）。
        """
        if len(self.init_states) > 1:
            return False

        for next_states in self.trans_map.values():
            if len(next_states) > 1:
                return False

        if strict:
            for state in self.states:
                for chara in self.charas:
                    if len(self.trans_map.get((state, chara), ())) != 1:
                        return False

        return True

    def determinize(self, to_type="dfa", complete=False):
        """
        使用子集构造法将当前nfa转换为等价的确定型自动机。
        to_type=="dfa"（默认）时返回dfa，to_type=="nfa"时返回nfa。
        complete==True时补齐死状态，使得每个(状态,字符)都有转移（补集运算需要）。
        """

        # 初始化：起始状态是初始状态的集合
        start_set = frozenset(self.init_states)

        # 映射：状态集合 -> 新的状态名称
        state_mapping = {start_set: 0}

        # 新自动机的组件
        new_states = [0]
        new_trans_map = {}

        # 使用队列进行BFS遍历所有可达的状态子集
        queue = deque([start_set])
        state_counter = 1

        while queue:
            current_set = queue.popleft()
            current_id = state_mapping[current_set]

            # 对每个字符计算转移
            for chara in self.charas:

                # 计算当前状态集合在字符chara下的所有下一状态
                next_set = frozenset(next_state for state in current_set
                                     for next_state in self.trans_map.get((state, chara), ()))

                # 如果没有转移则跳过（将被视为转入一个死状态）
                if not next_set:
                    continue

                # 如果这个状态集合尚未见过，创建新状态
                if next_set not in state_mapping:
                    state_mapping[next_set] = state_counter
                    new_states.append(state_counter)
                    queue.append(next_set)
                    state_counter += 1

                # 添加转移：当前状态 -> 字符 -> {下一状态}
                new_trans_map[(current_id, chara)] = {state_mapping[next_set]}

            if len(new_states) + len(queue) > self.max_state_num:
                print(f"\033[31mState num overflow when calculating det({self.name})!\033[0m")
                raise OverflowError

        # 补齐死状态
        if complete:
            dead_id = None
            for state_id in list(new_states):
                for chara in self.charas:
                    if (state_id, chara) not in new_trans_map:
                        if dead_id is None:
                            dead_id = state_counter
                            state_counter += 1
                            new_states.append(dead_id)
                        new_trans_map[(state_id, chara)] = {dead_id}

            if dead_id is not None:
                for chara in self.charas:
                    new_trans_map[(dead_id, chara)] = {dead_id}

        # 状态集合与终止状态集相交的新状态即为终止状态
        new_final_states = {state_mapping[state_set] for state_set in state_mapping
                            if state_set & self.final_states}

        new_dfa = dfa(trans_map=new_trans_map,
                      charas=self.charas.copy(),
                      states=new_states,
                      init_states={0},
                      final_states=new_final_states,
                      name=f"det({self.name})",
                      max_state_num=self.max_state_num)

        if to_type == "nfa" or to_type is nfa:
            return new_dfa.to_nfa()

        return new_dfa

    """↓↓关于可达性的属性和方法："""

    def adjacency(self, backward=False) -> dict:
        """邻接表{状态: set(相邻状态)}"""
        adjacency = {}
        if not backward:
            for (state, chara), next_states in self.trans_map.items():
                adjacency.setdefault(state, set()).update(next_states)
        else:
            for (state, chara), next_states in self.trans_map.items():
                for next_state in next_states:
                    adjacency.setdefault(next_state, set()).add(state)
        return adjacency

    def neighbor_states(self, states, backward=None) -> set:
        """状态单步可到达的全部下一状态。
        backward==True表示反向，backward==None表示双向。
        """
        if backward is None:
            return self.neighbor_states(states, True) | self.neighbor_states(states, False)

        states = to_state_set(states)

        if not backward:
            return {next_state for (state, chara), next_state in self.enum_trans() if state in states}
        else:
            return {state for (state, chara), next_state in self.enum_trans() if next_state in states}

    def distance_from(self, init_states=None, backward=False):
        """
        计算从初始状态到每个状态的最短距离（最少转移步数），返回{状态: 最少转移步数}的dict，不可达的状态不会被包含在返回的字典中。
        """

        if init_states is None:
            if not backward:
                init_states = self.init_states
            else:
                init_states = self.final_states

        init_states = to_state_set(init_states)
        adjacency = self.adjacency(backward)

        # 使用BFS计算最短距离
        distances = {}
        queue = deque()

        # 初始化：所有初始状态的距离为0
        for init_state in sorted_items(init_states):
            if init_state not in distances:
                distances[init_state] = 0
                queue.append(init_state)

        # BFS遍历
        while queue:
            state = queue.popleft()
            dist = distances[state]

            # 检查所有从当前状态出发的转移
            for next_state in adjacency.get(state, ()):
                if next_state not in distances:
                    distances[next_state] = dist + 1
                    queue.append(next_state)

        return distances

    def reachable_states(self, init_states=None, backward=None) -> set:
        """
        （不限步数）可达的状态。
        backward==True表示反向，backward==None表示双向（既从初始状态可达、又能到达终止状态）。
        """

        if backward is None:
            return (self.reachable_states(init_states, True)
                    & self.reachable_states(init_states, False))
        else:
            return set(self.distance_from(init_states, backward).keys())

    def remove_unreachable_states(self, backward=None):
        """删除不可达的状态"""
        unreachable_states = set(self.states) - self.reachable_states(backward=backward)
        self.del_states(unreachable_states)

    """↓↓关于对词进行识别的属性和方法↓↓"""

    def next(self, states, word, final_states=None, reverse=False):
        """带状态词的单步转变，输出(下一状态集, 剩余词, 终止状态集)。"""

        states = to_state_set(states)
        word = self.to_local_word(word)

        # 词为空词，无剩余字符
        if len(word) == 0:
            return states, word, final_states

        # 词不是空词
        else:
            if not reverse:
                next_states = {next_state for state in states
                               for next_state in self.trans_map.get((state, word[0]), set())}

                return next_states, word[1:], final_states

            else:
                prev_states = self.backward_states(states, word[-1:])

                return prev_states, word[:-1], final_states

    def backward_states(self, states, word) -> set:
        """从states出发反向读取word后可到达的状态集（即哪些状态读取word后会进入states）。"""

        states = to_state_set(states)
        word = self.to_local_word(word)

        if len(word) == 0:
            return states

        # 反向邻接表：{下一状态: {(状态, 字符)}}
        reverse_adjacency = {}
        for (state, chara), next_states in self.trans_map.items():
            for next_state in next_states:
                reverse_adjacency.setdefault(next_state, set()).add((state, chara))

        for chara in reversed(word):
            states = {state for next_state in states
                      for (state, old_chara) in reverse_adjacency.get(next_state, ())
                      if old_chara == chara}
            if not states:
                break

        return states

    def final(self, states, word, final_states=None, reverse=False):
        """转变的最终结果：final_states为None时输出全部转变结果的集合，否则输出其与final_states是否相交的bool。"""

        states = to_state_set(states)
        word = self.to_local_word(word)

        # 反向读取
        if reverse:
            states = self.backward_states(states, word)

        # 正向读取
        else:
            for chara in word:
                next_states = set()
                for state in states:
                    next_states |= self.trans_map.get((state, chara), set())
                states = next_states

                if not states:
                    break

        if final_states is None:
            return states
        else:
            return len(states & to_state_set(final_states)) > 0

    def __call__(self, word, init_states=None, final_states=None):
        """自动机被调用，即以默认的初始和终止状态输出结果。"""

        if init_states is None:
            init_states = self.init_states
        if final_states is None:
            final_states = self.final_states

        return self.final(init_states, word, final_states)

    def accepts(self, word):
        """该自动机是否接受该词"""
        return bool(self(word))

    def __contains__(self, word):
        """该自动机是否接受该词"""
        return self.accepts(word)

    def enum_words(self, length=None, max_num=None, word_type=None):
        """枚举其接受的词。
        length为int时枚举该长度的词，为range/list/set时枚举其中各长度的词，为None时枚举长度<10的词。
        max_num为枚举数量的上限。word_type不为None时把输出的词转换成该格式。
        """
        """（用状态集合的BFS实现，会自动剪掉无法到达终止状态的分支）"""

        if length is None:
            length = range(10)
        if type(length) is int:
            lengths = {length}
        else:
            lengths = set(length)

        if not lengths:
            return

        max_len = max(lengths)
        live_states = self.reachable_states(backward=True)

        # 每一层是(词, 状态集合)，从初始状态出发
        frontier = [(self.empty_word, frozenset(state for state in self.init_states if state in live_states))]
        if not frontier[0][1]:
            return

        word_num = 0
        now_len = 0

        while frontier and now_len <= max_len:

            next_frontier = []

            for word, states in frontier:

                # 该词被接受
                if now_len in lengths and len(states & self.final_states) > 0:
                    yield word if word_type is None or word_type is self.word_type else convert_word(word, word_type)
                    word_num += 1
                    if max_num is not None and word_num >= max_num:
                        return

                # 在该词后继续添加字符
                if now_len < max_len:
                    for chara in self.charas:
                        next_states = set()
                        for state in states:
                            next_states |= self.trans_map.get((state, chara), set())
                        # 剪掉无法到达终止状态的分支
                        next_states &= live_states
                        if next_states:
                            next_frontier.append((word + chara, frozenset(next_states)))

            frontier = next_frontier
            now_len += 1

    @classmethod
    def words_acceptor(cls, words=None, name=None, charas=None):
        """确定特定的词集合的自动机（Trie）。
        words为None、[]或set()时为空语言；words为""或()时只含空词。
        词的格式可以是str或tuple，自动机内部使用与字符格式一致的词格式。
        charas不为None时以其为字符表，并把每个词按该字符表切分成字符序列
        （字符表含元组字符时，用它可以消除"词"与"字符"的歧义）。
        """

        if words is None:
            words = set()

        words = to_word_set(words)

        if len(words) == 0:
            return cls(trans_map={}, charas=list(charas) if charas else [], states=[0],
                       init_states={0}, final_states=set(), name="A_()")

        if charas is None:
            # 先按tuple格式取出全部字符
            charas = sorted_items({chara
                                   for word in words
                                   for chara in (word if type(word) is tuple else tuple(word))})
        else:
            charas = list(charas)

        # 统一所有词的格式：字符都是str时用str格式的词，否则用tuple格式的词
        to_type = str if all(type(chara) is str for chara in charas) else tuple
        if to_type is str:
            words = {word_to_str(word) for word in words}
        else:
            words = {segment_word(word, charas) for word in words}

        if name is None:
            name = f"A_({'|'.join(word_str(word) for word in sorted_items(words))})"

        # 构建Trie节点：{(状态, 字符): 下一状态}
        trie = {}
        final_states = set()

        # 初始状态
        init_state = 0
        state_counter = 1

        # 插入所有词
        for word in sorted_items(words):
            current_state = init_state

            if len(word) == 0:  # 空串
                final_states.add(init_state)
                continue

            for chara in word:
                if (current_state, chara) not in trie:
                    trie[(current_state, chara)] = state_counter
                    state_counter += 1
                current_state = trie[(current_state, chara)]

            final_states.add(current_state)

        # 转换为自动机（Trie总是确定性的）
        states = list(range(state_counter))
        trans_map = {key: {next_state} for key, next_state in trie.items()}

        return cls(trans_map=trans_map, charas=charas, states=states,
                   init_states={init_state}, final_states=final_states, name=name)

    @classmethod
    def from_expr(cls, expr, to_type=None, charas=None):
        """根据正则表达式构造自动机。
        表达式支持：|（并，优先级最低）、&（交）、@或省略（拼接）、*（Kleene星号）、
        +（Kleene加号）、~（补集）、(...)（分组）。
        注意：连续的普通字符视为一个词（如ab是词"ab"而不是a与b的拼接），拼接请用@或括号。
        to_type为None时结果为cls，为"dfa"时结果为dfa；charas为指定的字符表（~运算需要完整字符表）。
        """

        # 非字符串输入视为词集合
        if type(expr) is not str:
            return cls.words_acceptor(expr)

        if charas is None:
            charas = sorted_items({ch for ch in expr if ch not in EXPR_SYMBS})
        else:
            charas = list(charas)

        parser = _ExprParser(expr, charas)
        new_fa = parser.parse()

        if to_type is None:
            to_type = cls

        if to_type == "dfa" or to_type is dfa or (isinstance(to_type, type) and issubclass(to_type, dfa)):
            return new_fa.to_dfa()

        return new_fa.to_nfa()

    @classmethod
    def from_regex(cls, expr, to_type=None, charas=None):
        """from_expr的别名"""
        return cls.from_expr(expr, to_type=to_type, charas=charas)

    """↓↓关于枚举和修改其结构的属性和方法↓↓"""

    def add_trans(self, trans, next_symb=None):
        """添加转变。允许的形式有：
            add_trans((状态, 字符), 下一状态)
            add_trans(((状态, 字符), 下一状态))
            add_trans([((状态, 字符), 下一状态), ...])
        """

        if next_symb is not None:
            trans = (trans, next_symb)

        if type(trans) is tuple and len(trans) == 2 and type(trans[0]) is tuple:
            key, value = trans
            next_states = self.normalize_next_states(value)

            if key in self.trans_map:
                self.trans_map[key] |= next_states
            else:
                self.trans_map[key] = set(next_states)

        else:
            for one_trans in self.iter_trans(trans):
                self.add_trans(one_trans)

    @staticmethod
    def iter_trans(trans):
        """把多个转变的容器转换成可迭代对象"""
        if type(trans) is str:
            raise ValueError(f"无法识别的转变：{trans!r}")
        try:
            return iter(trans)
        except TypeError:
            raise ValueError(f"无法识别的转变：{trans!r}")

    def enum_trans(self, sort=False):
        """以二元组 ((状态, 字符), 下一状态) 的格式枚举所有转变"""
        if sort:
            trans_list = list(self.enum_trans())
            try:
                trans_list.sort()
            except TypeError:
                trans_list.sort(key=lambda trans: str(trans))
            for trans in trans_list:
                yield trans
        else:
            for (state, chara), next_states in self.trans_map.items():
                for next_state in next_states:
                    yield (state, chara), next_state

    @property
    def _state_set(self):
        """状态集合的缓存（用于加速add_states）"""
        cache = getattr(self, "_state_set_cache", None)
        if (cache is None or len(cache) != len(self.states)
                or (self.states and self.states[0] not in cache)):
            cache = set(self.states)
            self._state_set_cache = cache
        return cache

    @property
    def _chara_set(self):
        """字符集合的缓存（用于加速to_local_word）"""
        cache = getattr(self, "_chara_set_cache", None)
        if (cache is None or len(cache) != len(self.charas)
                or (self.charas and self.charas[0] not in cache)):
            cache = set(self.charas)
            self._chara_set_cache = cache
        return cache

    def add_states(self, num: int | None = None, old_state=None):
        """以某个状态作为基底添加新状态。
        num为None时添加一个新状态并返回它，否则添加num个新状态并返回这些新状态的列表。
        """

        state_type = self.state_type
        state_set = self._state_set
        new_state_list = []

        # 状态为整数格式：用计数提示避免每次从头查找，新状态取未出现的新自然数
        if state_type is int:

            hint = self._int_state_hint
            if hint is None:
                hint = max((state for state in self.states if type(state) is int), default=-1) + 1

            for _ in range(1 if num is None else num):
                while hint in state_set:
                    hint += 1
                new_state = hint
                self.states.append(new_state)
                state_set.add(new_state)
                new_state_list.append(new_state)
                hint += 1

            self._int_state_hint = hint

        # 状态为str或tuple格式：以old_state为基底生成新状态
        else:

            for _ in range(1 if num is None else num):

                if old_state is not None:
                    base = old_state
                elif state_type is tuple:
                    base = (len(self.states),)
                else:
                    base = f"s{len(self.states)}"

                new_state = make_state(base, state_type, state_set)
                self.states.append(new_state)
                state_set.add(new_state)
                new_state_list.append(new_state)

        if num is None:
            return new_state_list[0]
        return new_state_list

    def del_states(self, deleted_states):
        """删除若干个状态，并连带删除相关的转变"""

        deleted_states = to_state_set(deleted_states)

        self.states = [state for state in self.states if state not in deleted_states]
        self._state_set_cache = None
        self._int_state_hint = None

        self.init_states = {state for state in self.init_states if state not in deleted_states}
        self.final_states = {state for state in self.final_states if state not in deleted_states}

        for key in list(self.trans_map.keys()):

            if key[0] in deleted_states:
                del self.trans_map[key]
            else:
                next_states = {next_state for next_state in self.trans_map[key]
                               if next_state not in deleted_states}
                if next_states:
                    self.trans_map[key] = next_states
                else:
                    del self.trans_map[key]

    """↓↓正则语言的基础运算：↓↓"""

    def __or__(self, other):
        """并集"""

        if not isinstance(other, nfa):
            return NotImplemented

        both_dfa = isinstance(self, dfa) and isinstance(other, dfa)

        # 统一字符格式与字符表
        fa1, fa2 = align_fa(self, other)

        # 新自动机保留左侧自动机的全部状态和转变
        new_fa = fa1.to_nfa().copy(name=f"({self.name}|{other.name})")

        # 添加右侧自动机的字符，重复的字符不再添加
        new_fa.charas = list(fa1.charas)

        # 添加右侧自动机的状态，重复的状态要被重命名
        state_map = {}

        def mapped_state(state):
            if state not in state_map:
                state_map[state] = new_fa.add_states(old_state=state)
            return state_map[state]

        for state in fa2.states:
            mapped_state(state)

        # 添加右侧自动机的转变，其中的状态要进行重命名
        for (state, chara), next_states in fa2.trans_map.items():
            for next_state in next_states:
                new_fa.add_trans((state_map[state], chara), mapped_state(next_state))

        # 添加右侧自动机的初始，终止状态
        for init_state in fa2.init_states:
            new_fa.init_states.add(mapped_state(init_state))
        for final_state in fa2.final_states:
            new_fa.final_states.add(mapped_state(final_state))

        # 两个dfa的并仍是dfa
        if both_dfa:
            return new_fa.determinize(to_type="dfa")

        return new_fa

    def __and__(self, other):
        """交集"""

        if not isinstance(other, nfa):
            return NotImplemented

        both_dfa = isinstance(self, dfa) and isinstance(other, dfa)

        # 统一字符格式与字符表
        fa1, fa2 = align_fa(self, other)
        new_charas = list(fa1.charas)

        # 构造笛卡尔积的初始状态集
        init_states = {(s1, s2) for s1 in fa1.init_states for s2 in fa2.init_states}

        # 使用BFS构造所有可达的状态对和转移
        trans_map = {}
        final_states = set()
        visited = set()
        queue = deque(sorted_items(init_states))

        while queue:
            current_pair = queue.popleft()

            if current_pair in visited:
                continue

            visited.add(current_pair)
            s1, s2 = current_pair

            # 如果两个状态都是终止状态，则状态对是终止状态
            if s1 in fa1.final_states and s2 in fa2.final_states:
                final_states.add(current_pair)

            # 对每个字符计算转移
            for chara in new_charas:

                # 笛卡尔积：所有可能的下一状态对
                next_pairs = {(ns1, ns2)
                              for ns1 in fa1.trans_map.get((s1, chara), set())
                              for ns2 in fa2.trans_map.get((s2, chara), set())}

                if next_pairs:
                    trans_map[(current_pair, chara)] = next_pairs

                    # 将未访问的状态对加入队列
                    for pair in sorted_items(next_pairs):
                        if pair not in visited:
                            queue.append(pair)

            if len(visited) + len(queue) > self.max_state_num:
                print(f"\033[31mState num overflow when calculating ({self.name}&{other.name})!\033[0m")
                raise OverflowError

        # 新状态为所有可达状态
        new_states = list(visited)

        # 两个dfa的交仍是dfa（笛卡尔积自动机是确定的）
        new_cls = dfa if both_dfa else nfa

        return new_cls(trans_map=trans_map, charas=new_charas, states=new_states,
                       init_states=init_states, final_states=final_states,
                       name=f"({self.name}&{other.name})", max_state_num=self.max_state_num)

    def __invert__(self):
        """确定原语言补集的dfa"""

        # 非确定则先确定化，同时补齐死状态以保证补集的正确性
        new_fa = self.determinize(to_type="dfa", complete=True)

        # 终止状态取补
        new_fa.final_states = {state for state in new_fa.states if state not in new_fa.final_states}

        new_fa.name = f"~{self.name}"

        return new_fa

    def is_empty(self):
        """检查语言是否为空（使用图搜索）"""

        adjacency = self.adjacency()

        visited = set()  # 已到达过的状态
        queue = deque(sorted_items(self.init_states))  # 等待检查的状态

        while queue:
            state = queue.popleft()

            if state in visited:
                continue
            visited.add(state)

            # 如果到达终止状态，语言非空
            if state in self.final_states:
                return False

            # BFS搜索所有可能的转移
            for next_state in adjacency.get(state, ()):
                if next_state not in visited:
                    queue.append(next_state)

        return True  # 没有找到可达的终止状态

    def is_disjoint(self, other):
        """检查两个自动机的语言是否不交"""

        if not isinstance(other, nfa):
            return NotImplemented

        fa1, fa2 = align_fa(self, other)
        charas = fa1.charas

        visited = set()  # 已到达过的状态对
        queue = deque(sorted_items((state1, state2)
                                   for state1 in fa1.init_states
                                   for state2 in fa2.init_states))  # 等待检查的状态对

        while queue:
            state_pair = queue.popleft()

            if state_pair in visited:
                continue
            visited.add(state_pair)

            # 如果同时到达终止状态，两者的交非空
            state1, state2 = state_pair
            if state1 in fa1.final_states and state2 in fa2.final_states:
                return False

            # BFS搜索所有可能的转移
            for chara in charas:
                for next_state1 in fa1.trans_map.get((state1, chara), ()):
                    for next_state2 in fa2.trans_map.get((state2, chara), ()):
                        if (next_state_pair := (next_state1, next_state2)) not in visited:
                            queue.append(next_state_pair)

        return True  # 没有找到同时可达的终止状态

    def __matmul__(self, other):
        """语言拼接（与*一致，便于与表达式中@的写法统一）"""
        return self * other

    def __mul__(self, other):
        """语言拼接以及特殊运算（重复，Kleene加号与Kleene星号）"""

        # 与特殊运算符号拼接
        if type(other) is str:

            # Kleene星号
            if other == "*" or other == "+":
                return self.kleene_star(other)

            raise TypeError(f"无法将自动机与字符串{other!r}拼接，星号/加号请用'*'/'+'")

        # 重复
        if type(other) is int:

            if other < 0:
                raise ValueError(f"重复次数不能为负：{other}")

            elif other == 0:
                return self.words_acceptor("", name="A_()")

            elif other == 1:
                return self.copy()

            else:
                new_fa = self
                for _ in range(other - 1):
                    new_fa = new_fa * self
                new_fa.name = f"({self.name}^{other})"

                return new_fa

        if not isinstance(other, nfa):
            return NotImplemented

        both_dfa = isinstance(self, dfa) and isinstance(other, dfa)

        # 统一字符格式与字符表
        fa1, fa2 = align_fa(self, other)

        # 新自动机保留左侧自动机的全部状态和转变
        new_fa = fa1.to_nfa().copy(name=f"({self.name}{other.name})")

        # 添加右侧自动机的字符，重复的字符不再添加
        new_fa.charas = list(fa1.charas)

        # 添加右侧自动机的状态，重复的状态要被重命名
        state_rename = {}

        def renamed_state(state):
            if state not in state_rename:
                state_rename[state] = new_fa.add_states(old_state=state)
            return state_rename[state]

        for state in fa2.states:
            renamed_state(state)

        # 添加右侧自动机的转变，其中的状态要进行重命名
        for (state, chara), next_states in fa2.trans_map.items():
            for next_state in next_states:
                new_fa.add_trans((state_rename[state], chara), renamed_state(next_state))

        # 如果self接受空串，则other的初始状态也是初始状态
        if len(fa1.init_states & fa1.final_states) > 0:
            for state in fa2.init_states:
                new_fa.init_states.add(renamed_state(state))

        # 终止状态改为右侧自动机的终止状态，但如果other接受空串，则self的终止状态也是终止状态
        new_fa.final_states = {renamed_state(state) for state in fa2.final_states}
        if len(fa2.init_states & fa2.final_states) > 0:
            new_fa.final_states = set(fa1.final_states) | new_fa.final_states

        # 所有转入self的终止状态的转移都添加转入other的初始状态的翻版
        renamed_init_states = {renamed_state(state) for state in fa2.init_states}
        for (state, chara), next_state in fa1.enum_trans():
            if next_state in fa1.final_states:
                for new_next_state in renamed_init_states:
                    new_fa.add_trans((state, chara), new_next_state)

        # 两个dfa的拼接仍是dfa
        if both_dfa:
            return new_fa.determinize(to_type="dfa")

        return new_fa

    def kleene_star(self, star="*"):
        """Kleene星号（零次或多次重复），star不为"*"时为Kleene加号（大于零次重复）"""

        new_fa = self.to_nfa().copy(name=f"({self.name}{star})")

        # 所有转入终止状态的转移都添加转入初始状态的翻版
        for (state, chara), next_state in self.enum_trans():
            if next_state in self.final_states:
                for new_next_state in new_fa.init_states:
                    new_fa.add_trans((state, chara), new_next_state)

        # 如果是*且原本不接受空词，添加空词
        if star == "*" and (not new_fa(self.empty_word)):
            new_state = new_fa.add_states()
            new_fa.init_states.add(new_state)
            new_fa.final_states.add(new_state)

        return new_fa

    def __sub__(self, other):
        """差集"""

        if not isinstance(other, nfa):
            return NotImplemented

        # 统一字符表，保证补集是相对于两个自动机的字符表的并集
        fa1, fa2 = align_fa(self, other)

        new_fa = fa1 & (~fa2)
        new_fa.name = f"({self.name}-{other.name})"

        return new_fa

    def __le__(self, other):
        """判断是否被包含"""

        if not isinstance(other, nfa):
            return NotImplemented

        # 统一字符表，保证补集是相对于两个自动机的字符表的并集
        fa1, fa2 = align_fa(self, other)

        return (fa1 & (~fa2)).is_empty()

    def __lt__(self, other):
        """判断是否被真包含"""

        if not isinstance(other, nfa):
            return NotImplemented

        return self <= other and (not other <= self)

    def __eq__(self, other):
        """判断是否相等"""

        if not isinstance(other, nfa):
            return NotImplemented

        return self <= other and other <= self

    def left_quot(self, prefixes):
        """左商"""

        prefixes = {self.to_local_word(prefix) for prefix in to_word_set(prefixes)}

        new_init_states = set()
        for prefix in prefixes:
            new_init_states |= self.final(self.init_states, prefix)

        new_fa = self.copy(f"(({'|'.join(word_str(prefix) for prefix in sorted_items(prefixes))})\\{self.name})")
        new_fa.init_states = new_init_states

        new_fa.remove_unreachable_states()

        return new_fa.fit_type()

    def reverse(self):
        """翻转"""

        reversed_fa = nfa(trans_map={},
                          charas=self.charas.copy(),
                          states=self.states.copy(),
                          init_states=self.final_states.copy(),
                          final_states=self.init_states.copy(),
                          name=f"{self.name}^R",
                          max_state_num=self.max_state_num)

        for (state, chara), next_state in self.enum_trans():
            reversed_fa.add_trans((next_state, chara), state)

        return reversed_fa.fit_type(prefer_dfa=isinstance(self, dfa))

    def right_quot(self, suffixes):
        """右商"""

        suffixes = {self.to_local_word(suffix) for suffix in to_word_set(suffixes)}

        new_final_states = set()
        for suffix in suffixes:
            new_final_states |= self.backward_states(self.final_states, suffix)
        new_final_states &= set(self.states)

        new_fa = self.copy(f"(({'|'.join(word_str(suffix) for suffix in sorted_items(suffixes))})/{self.name})")
        new_fa.final_states = new_final_states

        new_fa.remove_unreachable_states()

        return new_fa.fit_type()

    def comp_rewrite(self, rewrite):
        """本自动机与一个重写进行复合（这是本项目最关键的函数）。
        rewrite为(原词, 新词)或(原词, 新词, 定位方式)，定位方式为：
            "subword"（原词可以出现在任意位置，默认）
            "prefix"（原词必须出现在词首）
            "suffix"（原词必须出现在词尾）
        也接受由多个重写组成的列表/元组，此时返回各个复合结果的并。
        """

        # 多个重写，分别重写后取并
        if not is_rewrite(rewrite):

            rewrites = list(rewrite)

            if len(rewrites) == 0:
                new_fa = nfa.words_acceptor([])
                new_fa.charas = self.charas.copy()
                return new_fa

            new_fa = self.comp_rewrite(rewrites[0])
            for now_rewrite in rewrites[1:]:
                new_fa = new_fa | self.comp_rewrite(now_rewrite)

            return new_fa.fit_type()

        # 单个重写
        if len(rewrite) == 2:
            word, next_word = rewrite
            fix_type = "subword"
        else:
            word, next_word, fix_type = rewrite[:3]

        word = self.to_local_word(word)
        next_word = self.to_local_word(next_word)

        if fix_type not in {"subword", "prefix", "suffix"}:
            raise ValueError(f"无法识别的重写定位方式：{fix_type!r}")
        if len(word) == 0:
            raise ValueError("重写的原词不能为空词")

        new_fa = self.to_nfa().copy(name=f"({self.name}@({word_str(word)}->{word_str(next_word)}))")

        states_layers = [[] for _ in range(len(next_word) + 2)]
        states_layers[0] = self.states.copy()
        '''各层的状态层数等于重写后的字符数+2'''

        # 向自动机和列表中添加每层的状态
        for i in range(1, len(states_layers)):
            states_layers[i] = new_fa.add_states(len(self.states))

        # 状态在状态表中的下标，用来在各层之间对应
        state_index = {state: i for i, state in enumerate(self.states)}

        def layer_state(layer_index, state):
            return states_layers[layer_index][state_index[state]]

        # 终止状态是对应的最后一层的状态
        new_fa.final_states = {layer_state(-1, state) for state in self.final_states if state in state_index}

        # 如果是前缀重写，原词必须出现在词首，第0层不参与读取
        if fix_type == "prefix":
            new_fa.trans_map = {}
            new_fa.init_states = set()

        # 第0层的所有状态都转入其转入的下一状态对应的下一层的状态
        if fix_type != "prefix":
            for (state, chara), next_state in self.enum_trans():
                post_states = self.final(next_state, word)
                # print(f"{state}·{chara}->{next_state}, post_state={post_states}")
                for post_state in post_states:
                    if post_state in state_index:
                        new_fa.add_trans((state, chara), layer_state(1, post_state))

        # 初始状态包括第0层的状态（如果有）空转移到第1层到达的状态。
        for init_state in self.init_states:
            post_states = self.final(init_state, word)
            # print(f"{state}·{chara}->{next_state}, post_state={post_states}")
            for post_state in post_states:
                if post_state in state_index:
                    new_fa.init_states.add(layer_state(1, post_state))

        # 第1到倒数第二层中的状态读取正确的字符时转入下一层的对应状态
        for layer_index in range(1, len(states_layers) - 1):
            layer_states = states_layers[layer_index]
            for state_index_in_layer, state in enumerate(layer_states):
                chara = next_word[layer_index - 1]
                next_state = states_layers[layer_index + 1][state_index_in_layer]
                new_fa.add_trans((state, chara), next_state)

        # 最后一层的转变与原自动机的转变一致。如果是后缀重写，则不再有这样的转变。
        if fix_type != "suffix":
            for (state, chara), next_state in self.enum_trans():
                if state in state_index and next_state in state_index:
                    mapped_state = layer_state(-1, state)
                    mapped_next_state = layer_state(-1, next_state)
                    new_fa.add_trans((mapped_state, chara), mapped_next_state)

        # 化简后输出
        new_fa.remove_unreachable_states()

        if len(new_fa.states) > new_fa.max_state_num:
            print(f"\033[31mState num overflow when calculating rewrite of {self.name}!\033[0m")
            raise OverflowError

        return new_fa.fit_type(prefer_dfa=isinstance(self, dfa))


class dfa(nfa):
    """
    确定性有限状态自动机。与nfa的区别在于：
      1. 初始状态唯一（init_states中的元素不多于一个）；
      2. 每个(状态, 字符)最多有一个下一状态（内部仍以单元素set存储，以便复用nfa的全部函数）；
      3. 转变映射可以直接用 {(状态, 字符): 下一状态} 的简写格式构造。
    nfa的全部函数对dfa同样有效；两个dfa之间的交、并、补、差运算的结果仍然是dfa。
    """

    def __init__(self, trans_map: dict | tuple = None, charas: str | list = None, states: str | list = None,
                 init_states: str | set = None, final_states: str | set = None, name="D",
                 max_state_num=MAX_STATE_NUM):

        super().__init__(trans_map, charas, states, init_states, final_states, name, max_state_num)

        # 确定性检查
        for key, next_states in self.trans_map.items():
            if len(next_states) > 1:
                raise ValueError(f"dfa的转变{key}有多于一个的下一状态：{next_states}")

        if len(self.init_states) > 1:
            raise ValueError(f"dfa只能有一个初始状态：{self.init_states}")

    '''↓↓关于确定性的属性和方法：↓↓'''

    @classmethod
    def from_nfa(cls, other, name=None, complete=False):
        """由nfa确定化得到dfa"""
        other: nfa
        new_dfa = other.to_dfa(complete=complete)
        new_dfa.name = other.name if name is None else name
        return new_dfa

    def next_state(self, state, chara, default=None):
        """单个状态读取单个字符后的唯一后继状态"""
        next_states = self.trans_map.get((state, chara))
        if not next_states:
            return default
        return any_item(next_states)

    @property
    def next_map(self) -> dict:
        """{(状态, 字符): 下一状态}格式的转变映射"""
        return {key: any_item(next_states) for key, next_states in self.trans_map.items()}

    @property
    def is_complete(self):
        """是否为完整的dfa（每个(状态,字符)都有转移）"""
        return self.is_deterministic(strict=True)

    def complete(self):
        """补齐死状态，使得每个(状态, 字符)都有转移，返回新的dfa"""

        new_dfa = self.copy()

        dead_state = None
        for state in list(new_dfa.states):
            for chara in new_dfa.charas:
                if (state, chara) not in new_dfa.trans_map:
                    if dead_state is None:
                        dead_state = new_dfa.add_states()
                    new_dfa.add_trans((state, chara), dead_state)

        if dead_state is not None:
            for chara in new_dfa.charas:
                new_dfa.add_trans((dead_state, chara), dead_state)

        return new_dfa

    def is_deterministic(self, strict=False):
        """dfa总是（非严格）确定的。strict==True时检查转移函数是否完整。"""
        return super().is_deterministic(strict)

    def determinize(self, to_type="dfa", complete=False):
        """dfa本身已经是确定的，直接返回副本"""

        new_dfa = self.copy()

        if complete:
            new_dfa = new_dfa.complete()

        if to_type == "nfa" or to_type is nfa:
            return new_dfa.to_nfa()

        return new_dfa

    def minimize(self):
        """最小化（Moore划分细化），返回状态数最少的等价完整dfa"""

        # 先补齐转移函数，使得每个状态对每个字符都有转移
        new_dfa = self.complete()

        # 删除从初始状态不可达的状态
        unreachable_states = set(new_dfa.states) - new_dfa.reachable_states(backward=False)
        new_dfa.del_states(unreachable_states)

        states = list(new_dfa.states)
        state_index = {state: i for i, state in enumerate(states)}
        charas = list(new_dfa.charas)

        # 转移的索引表示
        next_index = {}
        for i, state in enumerate(states):
            for chara in charas:
                next_index[(i, chara)] = state_index[new_dfa.next_state(state, chara)]

        # 初始划分：终止状态与非终止状态
        final_indexes = {state_index[state] for state in states if state in new_dfa.final_states}
        parts = []
        non_final_indexes = [i for i in range(len(states)) if i not in final_indexes]
        if non_final_indexes:
            parts.append(non_final_indexes)
        if final_indexes:
            parts.append(sorted(final_indexes))

        # 反复细化划分，直到不再变化
        block_of = [0] * len(states)
        while True:
            for block_id, part in enumerate(parts):
                for i in part:
                    block_of[i] = block_id

            new_parts = []
            for part in parts:
                groups = {}
                for i in part:
                    signature = tuple(block_of[next_index[(i, chara)]] for chara in charas)
                    groups.setdefault(signature, []).append(i)
                new_parts.extend(groups.values())

            if len(new_parts) == len(parts):
                break
            parts = new_parts

        for block_id, part in enumerate(parts):
            for i in part:
                block_of[i] = block_id

        # 以划分的块作为新状态
        new_states = list(range(len(parts)))
        trans_map = {}
        for i in range(len(states)):
            for chara in charas:
                trans_map[(block_of[i], chara)] = block_of[next_index[(i, chara)]]

        new_init_states = {block_of[state_index[any_item(new_dfa.init_states)]]}
        new_final_states = {block_of[i] for i in final_indexes}

        return dfa(trans_map=trans_map,
                   charas=charas,
                   states=new_states,
                   init_states=new_init_states,
                   final_states=new_final_states,
                   name=f"min({self.name})",
                   max_state_num=self.max_state_num)

    def __invert__(self):
        """补集（dfa无需确定化）"""

        new_dfa = self.complete()

        # 终止状态取补
        new_dfa.final_states = {state for state in new_dfa.states if state not in new_dfa.final_states}

        new_dfa.name = f"~{self.name}"

        return new_dfa

    '''↓↓关于修改其结构的属性和方法：↓↓'''

    def add_trans(self, trans, next_symb=None):
        """添加转变（dfa要求每个(状态, 字符)最多有一个下一状态）"""

        if next_symb is not None:
            trans = (trans, next_symb)

        if type(trans) is tuple and len(trans) == 2 and type(trans[0]) is tuple:
            key, value = trans
            next_states = self.normalize_next_states(value)

            if len(next_states) > 1:
                raise ValueError(f"dfa不允许一个(状态, 字符)对应多个下一状态：{key}->{next_states}")

            if key in self.trans_map and self.trans_map[key] != next_states:
                raise ValueError(f"dfa的转变冲突：{key}已有{self.trans_map[key]}，不能改为{next_states}")

            self.trans_map[key] = set(next_states)

        else:
            for one_trans in self.iter_trans(trans):
                self.add_trans(one_trans)


class _ExprParser:
    """正则表达式的递归下降解析器。
    表达式支持：|（并，优先级最低）、&（交）、@或省略（拼接）、*（Kleene星号）、
    +（Kleene加号）、~（补集）、(...)（分组）。
    连续的普通字符视为一个词（如ab是词"ab"而不是a与b的拼接），拼接请用@或括号。
    """

    def __init__(self, text: str, charas: list = None):
        self.text = text
        self.pos = 0
        if charas is None:
            charas = sorted_items({ch for ch in text if ch not in EXPR_SYMBS})
        self.charas = list(charas)

    def peek(self):
        """当前位置的字符，超出末尾时为空串"""
        return self.text[self.pos] if self.pos < len(self.text) else ""

    def parse(self):
        """解析整个表达式"""
        new_fa = self.parse_union()

        if self.pos < len(self.text):
            raise ValueError(f"表达式{self.text!r}的{self.pos}处无法解析：{self.text[self.pos:]!r}")

        # 空表达式只接受空词
        if new_fa is None:
            new_fa = nfa.words_acceptor("", name="A_()")

        # 保证字符表完整（补集运算的需要）
        if self.charas:
            new_fa.charas = list(self.charas)

        return new_fa

    def parse_union(self):
        """并运算"""
        new_fa = self.parse_inter()

        while self.peek() == "|":
            self.pos += 1
            now_fa = self.parse_inter()
            if new_fa is None or now_fa is None:
                raise ValueError(f"表达式{self.text!r}的{self.pos}处|缺少操作数")
            new_fa = new_fa | now_fa

        return new_fa

    def parse_inter(self):
        """交运算"""
        new_fa = self.parse_concat()

        while self.peek() == "&":
            self.pos += 1
            now_fa = self.parse_concat()
            if new_fa is None or now_fa is None:
                raise ValueError(f"表达式{self.text!r}的{self.pos}处&缺少操作数")
            new_fa = new_fa & now_fa

        return new_fa

    def parse_concat(self):
        """拼接运算（@或省略）"""
        new_fa = None

        while True:
            chara = self.peek()

            if chara == "" or chara in ")|&":
                break

            # 显式的拼接符号
            if chara == "@":
                self.pos += 1
                if new_fa is None or self.peek() in ("", ")", "|", "&", "@"):
                    raise ValueError(f"表达式{self.text!r}的{self.pos - 1}处@缺少操作数")
                continue

            now_fa = self.parse_postfix()
            new_fa = now_fa if new_fa is None else new_fa * now_fa

        return new_fa

    def parse_postfix(self):
        """后缀运算（*与+）"""
        new_fa = self.parse_atom()

        while self.peek() in ("*", "+"):
            star = self.peek()
            self.pos += 1
            new_fa = new_fa.kleene_star(star)

        return new_fa

    def parse_atom(self):
        """原子（分组、补集或词）"""
        chara = self.peek()

        # 分组
        if chara == "(":
            self.pos += 1
            new_fa = self.parse_union()
            if new_fa is None:
                raise ValueError(f"表达式{self.text!r}的{self.pos}处缺少操作数")
            if self.peek() != ")":
                raise ValueError(f"表达式{self.text!r}的括号不匹配")
            self.pos += 1
            return new_fa

        # 补集
        elif chara == "~":
            self.pos += 1
            sub_fa = self.parse_postfix()
            if self.charas:
                sub_fa.charas = list(self.charas)
            return ~sub_fa

        # 缺少操作数
        elif chara == "" or chara in ")|&*+":
            raise ValueError(f"表达式{self.text!r}的{self.pos}处缺少操作数")

        # 连续的普通字符构成一个词
        else:
            start = self.pos
            while self.pos < len(self.text) and self.text[self.pos] not in EXPR_SYMBS:
                self.pos += 1
            return nfa.words_acceptor(self.text[start:self.pos])


def read_expr(expr, charas=None, to_type=None):
    """把表达式转换成对应的自动机结构（nfa.from_expr的别名）。
    默认给出nfa，to_type为"dfa"或dfa时给出dfa。
    """
    return nfa.from_expr(expr, to_type=to_type if to_type is not None else nfa, charas=charas)

