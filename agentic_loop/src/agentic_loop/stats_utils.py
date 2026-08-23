from dataclasses import dataclass

@dataclass(frozen=True)
class PurgeStats:
    removed_directories: int = 0
    reclaimed_bytes: int = 0

    def as_log_message(self) -> str:
        size = self.reclaimed_bytes
        units = ["B", "KiB", "MiB", "GiB"]
        unit_index = 0
        while size >= 1024 and unit_index < len(units) - 1:
            size /= 1024.0
            unit_index += 1
        size_str = f"{size:.1f} {units[unit_index]}" if self.reclaimed_bytes else "0 B"
        return (
            f"removed={self.removed_directories}, reclaimed={size_str}"
        )
