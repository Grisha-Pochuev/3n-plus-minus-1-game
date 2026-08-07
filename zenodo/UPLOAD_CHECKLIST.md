# Чек-лист публикации на Zenodo

Этот файл предназначен для ручной загрузки статьи. Репозиторий ничего не
публикует и не нажимает кнопку `Publish` автоматически.

## 1. Сначала зафиксировать выпуск

1. Убедиться, что `python audit.py` завершается строкой `AUDIT PASSED`.
2. Убедиться, что `lake build` проходит в каталоге `formal`.
3. Зафиксировать выпуск в Git. Перед публикацией также можно создать
   GitHub Release, например `v1.0.0`.
4. Запустить `python scripts/build_zenodo_bundle.py` из чистого committed checkout.
   Скрипт создаст каталог `dist/zenodo/` и контрольные суммы.

Не включайте в архив `.git`, `.tools`, локальные результаты экспериментов,
ключи доступа или токены Zenodo.

## 2. Создать черновик Zenodo

Откройте `New upload` на Zenodo и заполните поля:

| Поле | Значение |
|---|---|
| DOI | `10.5281/zenodo.21844684` |
| Resource type | `Publication` → `Preprint` |
| Title | `Termination under Optimal Play in the Two-Player 3n+/-1 Game` |
| Publication date | `2026-08-08` или фактическая дата первой публичной версии |
| Creator family name | `Pochuev` |
| Creator given name | `Grisha` |
| Language | `English` |
| License | `Creative Commons Attribution 4.0 International` |
| Access | `Open` |
| Version | `1.0.0` |
| Contact | `n_854@mail.ru` в описании/notes |

Скопируйте abstract, keywords, related identifier и notes из
`zenodo/deposit-metadata.json`.

Если у вас есть ORCID, добавьте его в Creator перед публикацией. Сейчас ORCID
не указан и не был выдуман.

## 3. Загрузить файлы

Из `dist/zenodo/` загрузите:

1. `termination-optimal-3n-plus-minus-1.pdf` — основной preview-файл;
2. `termination-optimal-3n-plus-minus-1-source.zip` — LaTeX, BibTeX и лицензия;
3. `verification-repository-snapshot.zip` — неизменяемый снимок кода,
   сертификатов, тестов и подробного доказательства;
4. `deposit-metadata.json` — точная копия полей записи;
5. `RELEASE.txt` — commit, ссылка на репозиторий, email и статус сертификата;
6. `SHA256SUMS.txt` — контрольные суммы всех остальных файлов.

Установите PDF как файл предварительного просмотра.

## 4. Связи и описание границы проверки

Добавьте related identifier:

```text
https://github.com/Grisha-Pochuev/3n-plus-minus-1-game
relation: Is supplemented by
resource type: Software
```

В notes обязательно оставьте предупреждение:

```text
The symbolic global certificate has status CONDITIONAL_MACHINE_CHECK.
It checks the declared global assembly but retains four explicit human
certificate-to-game obligations; see the trust-boundary document in the
repository snapshot.
```

## 5. DOI и финальная проверка

Запись опубликована с DOI
<https://doi.org/10.5281/zenodo.21844684>. Этот DOI добавлен в статью,
метаданные и файлы цитирования репозитория.

Перед `Publish`:

- открыть Zenodo Preview;
- скачать загруженный PDF и архивы обратно;
- сравнить SHA-256 с `SHA256SUMS.txt`;
- проверить автора, email, лицензию, дату, версию и GitHub-ссылку;
- проверить, что нигде не заявлена полная Lean-формализация;
- только после этого нажать `Publish`.
