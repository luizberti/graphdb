//! Interactive REPL using crossterm

use crossterm::{
    cursor::{self, MoveLeft, MoveRight, MoveToColumn},
    event::{self, Event, KeyCode, KeyEvent, KeyModifiers},
    execute,
    style::Print,
    terminal::{self, Clear, ClearType},
};
use std::io::{self, Write};

pub struct Repl {
    history: Vec<String>,
    history_idx: usize,
}

impl Repl {
    pub fn new() -> Self {
        Self {
            history: Vec::new(),
            history_idx: 0,
        }
    }

    pub fn run<F>(&mut self, mut handler: F) -> io::Result<()>
    where
        F: FnMut(&str) -> bool,
    {
        terminal::enable_raw_mode()?;
        let result = self.run_inner(&mut handler);
        terminal::disable_raw_mode()?;
        result
    }

    fn run_inner<F>(&mut self, handler: &mut F) -> io::Result<()>
    where
        F: FnMut(&str) -> bool,
    {
        let mut stdout = io::stdout();

        loop {
            execute!(stdout, Print("\r› "))?;
            stdout.flush()?;

            let Some(line) = self.read_line(&mut stdout)? else {
                // Ctrl-D on empty line
                execute!(stdout, Print("\r\n"))?;
                break;
            };

            let line = line.trim();
            if line.is_empty() {
                continue;
            }

            // Add to history
            if self.history.last().map(|s| s.as_str()) != Some(line) {
                self.history.push(line.to_string());
            }
            self.history_idx = self.history.len();

            // Handle command
            if !handler(line) {
                break;
            }
        }

        Ok(())
    }

    fn read_line(&mut self, stdout: &mut io::Stdout) -> io::Result<Option<String>> {
        let mut buf = String::new();
        let mut cursor_pos: usize = 0;
        let mut temp_history_idx = self.history_idx;
        let mut saved_input = String::new();

        loop {
            if let Event::Key(key) = event::read()? {
                match key {
                    KeyEvent {
                        code: KeyCode::Enter,
                        ..
                    } => {
                        execute!(stdout, Print("\r\n"))?;
                        return Ok(Some(buf));
                    }

                    KeyEvent {
                        code: KeyCode::Char('c'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        execute!(stdout, Print("^C\r\n"))?;
                        return Ok(Some(String::new()));
                    }

                    KeyEvent {
                        code: KeyCode::Char('d'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        if buf.is_empty() {
                            return Ok(None);
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Char('l'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        execute!(
                            stdout,
                            Clear(ClearType::All),
                            cursor::MoveTo(0, 0),
                            Print("› "),
                            Print(&buf),
                        )?;
                        cursor_pos = buf.len();
                    }

                    KeyEvent {
                        code: KeyCode::Char('a'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        if cursor_pos > 0 {
                            execute!(stdout, MoveToColumn(2))?;
                            cursor_pos = 0;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Char('e'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        if cursor_pos < buf.len() {
                            execute!(stdout, MoveToColumn((2 + buf.len()) as u16))?;
                            cursor_pos = buf.len();
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Char('u'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        if cursor_pos > 0 {
                            buf.drain(..cursor_pos);
                            execute!(
                                stdout,
                                MoveToColumn(2),
                                Clear(ClearType::UntilNewLine),
                                Print(&buf),
                                MoveToColumn(2),
                            )?;
                            cursor_pos = 0;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Char('k'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        if cursor_pos < buf.len() {
                            buf.truncate(cursor_pos);
                            execute!(stdout, Clear(ClearType::UntilNewLine))?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Char('w'),
                        modifiers: KeyModifiers::CONTROL,
                        ..
                    } => {
                        if cursor_pos > 0 {
                            let start = buf[..cursor_pos]
                                .trim_end()
                                .rfind(char::is_whitespace)
                                .map(|i| i + 1)
                                .unwrap_or(0);
                            buf.drain(start..cursor_pos);
                            cursor_pos = start;
                            self.redraw_line(stdout, &buf, cursor_pos)?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Char(c),
                        modifiers: KeyModifiers::NONE | KeyModifiers::SHIFT,
                        ..
                    } => {
                        buf.insert(cursor_pos, c);
                        cursor_pos += 1;
                        if cursor_pos == buf.len() {
                            execute!(stdout, Print(c))?;
                        } else {
                            self.redraw_line(stdout, &buf, cursor_pos)?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Backspace,
                        ..
                    } => {
                        if cursor_pos > 0 {
                            cursor_pos -= 1;
                            buf.remove(cursor_pos);
                            self.redraw_line(stdout, &buf, cursor_pos)?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Delete,
                        ..
                    } => {
                        if cursor_pos < buf.len() {
                            buf.remove(cursor_pos);
                            self.redraw_line(stdout, &buf, cursor_pos)?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Left,
                        ..
                    } => {
                        if cursor_pos > 0 {
                            cursor_pos -= 1;
                            execute!(stdout, MoveLeft(1))?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Right,
                        ..
                    } => {
                        if cursor_pos < buf.len() {
                            cursor_pos += 1;
                            execute!(stdout, MoveRight(1))?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Home,
                        ..
                    } => {
                        execute!(stdout, MoveToColumn(2))?;
                        cursor_pos = 0;
                    }

                    KeyEvent {
                        code: KeyCode::End,
                        ..
                    } => {
                        execute!(stdout, MoveToColumn((2 + buf.len()) as u16))?;
                        cursor_pos = buf.len();
                    }

                    KeyEvent {
                        code: KeyCode::Up, ..
                    } => {
                        if temp_history_idx > 0 {
                            if temp_history_idx == self.history.len() {
                                saved_input = buf.clone();
                            }
                            temp_history_idx -= 1;
                            buf = self.history[temp_history_idx].clone();
                            cursor_pos = buf.len();
                            self.redraw_line(stdout, &buf, cursor_pos)?;
                        }
                    }

                    KeyEvent {
                        code: KeyCode::Down,
                        ..
                    } => {
                        if temp_history_idx < self.history.len() {
                            temp_history_idx += 1;
                            buf = if temp_history_idx == self.history.len() {
                                saved_input.clone()
                            } else {
                                self.history[temp_history_idx].clone()
                            };
                            cursor_pos = buf.len();
                            self.redraw_line(stdout, &buf, cursor_pos)?;
                        }
                    }

                    _ => {}
                }
                stdout.flush()?;
            }
        }
    }

    fn redraw_line(
        &self,
        stdout: &mut io::Stdout,
        buf: &str,
        cursor_pos: usize,
    ) -> io::Result<()> {
        execute!(
            stdout,
            MoveToColumn(2),
            Clear(ClearType::UntilNewLine),
            Print(buf),
            MoveToColumn((2 + cursor_pos) as u16),
        )
    }
}

impl Default for Repl {
    fn default() -> Self {
        Self::new()
    }
}
