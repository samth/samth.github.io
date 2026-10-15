class TextBuffer {
  #text;
  #cursor = 0;

  constructor(text = "") {
    this.#text = text;
  }

  get length() {
    return this.#text.length;
  }

  get cursor() {
    return this.#cursor;
  }

  moveTo(position) {
    if (!Number.isInteger(position) || position < 0 || position > this.length) {
      throw new RangeError("Cursor position is out of bounds");
    }
    this.#cursor = position;
    return this;
  }

  insert(text) {
    this.#text = this.#text.slice(0, this.#cursor) + text + this.#text.slice(this.#cursor);
    this.#cursor += text.length;
    return this;
  }

  toString() {
    return this.#text;
  }
}

module.exports = { TextBuffer };
